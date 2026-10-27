// esp_loader.cpp - stage 2: chain + ESP + debug readout
#define WIN32_LEAN_AND_MEAN
#define NOMINMAX
#include <windows.h>
#include <cstdint>
#include <cstdio>
#include <cwchar>
#include <cmath>
#include <atomic>
#include <string>
#include <vector>

#pragma comment(lib, "gdi32.lib")
#pragma comment(lib, "user32.lib")

// ---------------- config ----------------
static bool  g_espOn     = true;
static bool  g_showDebug = true;
static float g_maxDist   = 800.f;
static float g_aimHeight = 1.72f;

// ---------------- math ----------------
struct Vec2 { float x = 0, y = 0; };
struct Vec3 { float x = 0, y = 0, z = 0; };

struct Player {
    float dist = 0.f, hp = 0.f, hpMax = 0.f;
    bool  onScreen = false;
    Vec2  head, foot;
};

struct Camera {
    Vec3 pos, right, up, fwd;
    float fov = 1.15f;
    bool  valid = false;
};

// ---------------- offsets (same keys as your offsets.ini) ----------------
struct Offsets {
    uintptr_t Game                  = 0x1D4FCE8;
    uintptr_t GameWorld             = 0x130;
    uintptr_t LocalPlayerController = 0x378;
    uintptr_t WeakPtr               = 0x8;
    uintptr_t LocalPlayerDelta      = 0x10;
    uintptr_t LocalPlayerCamera     = 0xD0;
    uintptr_t CameraPosition        = 0x68;
    uintptr_t InvertedViewRight     = 0x80;
    uintptr_t InvertedViewUp        = 0x8C;
    uintptr_t VectorViewForward     = 0x98;
    uintptr_t EntityList            = 0xF8;
    uintptr_t EntityCount           = 0x104;
    uintptr_t EntityPosition        = 0x8C;
    uintptr_t HealthChain1          = 0x158;
    uintptr_t HealthChain2          = 0xD8;
    uintptr_t Health                = 0x44;
    uintptr_t MaxHealth             = 0x40;
} g_off;

// ---------------- memory: in-process, plain dereference ----------------
static uintptr_t g_base = 0;

template <typename T>
static inline T Read(uintptr_t a) {
    if (a < 0x10000 || a > 0x7FFFFFFFFFFFull) return T{};
    __try {
        return *reinterpret_cast<T*>(a);
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        return T{};
    }
}

// ---------------- offset hunter ----------------
static std::vector<uintptr_t> g_gameHits;

static bool Readable(uintptr_t p, size_t size) {
    if (p < 0x10000 || p > 0x7FFFFFFFFFFFull) return false;
    if (p & 0x7) return false;
    MEMORY_BASIC_INFORMATION mbi{};
    if (!VirtualQuery(reinterpret_cast<LPCVOID>(p), &mbi, sizeof(mbi))) return false;
    if (mbi.State != MEM_COMMIT) return false;
    if (mbi.Protect & (PAGE_NOACCESS | PAGE_GUARD)) return false;
    uintptr_t end = reinterpret_cast<uintptr_t>(mbi.BaseAddress) + mbi.RegionSize;
    return p + size <= end;
}

// Walk the known member chain from every 8-byte-aligned value in the module.
// A hit means the camera landed on sane floats -> that value is the Game ptr.
static void HuntGame() {
    g_gameHits.clear();
    if (!g_base) return;

    auto dos = reinterpret_cast<PIMAGE_DOS_HEADER>(g_base);
    if (dos->e_magic != IMAGE_DOS_SIGNATURE) return;
    auto nt = reinterpret_cast<PIMAGE_NT_HEADERS>(g_base + dos->e_lfanew);

    auto sec = IMAGE_FIRST_SECTION(nt);
    for (int s = 0; s < nt->FileHeader.NumberOfSections; ++s) {
        if (!(sec[s].Characteristics & IMAGE_SCN_MEM_WRITE)) continue;
        size_t vsec = sec[s].Misc.VirtualSize;
        if (vsec < 8) continue;
        uintptr_t start = g_base + sec[s].VirtualAddress;

        for (size_t off = 0; off + sizeof(uintptr_t) <= vsec; off += sizeof(uintptr_t)) {
            uintptr_t v = Read<uintptr_t>(start + off);
            if (!Readable(v, 8)) continue;

            uintptr_t w = Read<uintptr_t>(v + g_off.GameWorld);
            if (!Readable(w, 8)) continue;

            uintptr_t cw = Read<uintptr_t>(w + g_off.LocalPlayerController);
            if (!Readable(cw, 8)) continue;

            uintptr_t c = Read<uintptr_t>(cw + g_off.WeakPtr);
            if (!Readable(c, 8)) continue;

            uintptr_t pc = Read<uintptr_t>((c - g_off.LocalPlayerDelta) + g_off.LocalPlayerCamera);
            if (!Readable(pc, 12)) continue;

            Vec3 pos = Read<Vec3>(pc + g_off.CameraPosition);
            Vec3 fwd = Read<Vec3>(pc + g_off.VectorViewForward);
            if (!std::isfinite(pos.x) || !std::isfinite(pos.y) || !std::isfinite(pos.z)) continue;
            if (!std::isfinite(fwd.x) || !std::isfinite(fwd.y) || !std::isfinite(fwd.z)) continue;
            float mag = sqrtf(pos.x * pos.x + pos.y * pos.y + pos.z * pos.z);
            if (mag < 1.f || mag > 200000.f) continue;

            // strong test: your own player is in this list, so an entity must
            // sit within 50 units of the camera
            uintptr_t list = Read<uintptr_t>(v + g_off.EntityList);
            int cnt = Read<int>(v + g_off.EntityCount);
            if (!Readable(list, 8) || cnt < 1 || cnt > 20000) continue;

            int lim = cnt < 256 ? cnt : 256;
            bool near = false;
            for (int i = 0; i < lim && !near; ++i) {
                uintptr_t e = Read<uintptr_t>(list + (uintptr_t)i * sizeof(uintptr_t));
                if (!Readable(e, 12)) continue;
                Vec3 ep = Read<Vec3>(e + g_off.EntityPosition);
                if (!std::isfinite(ep.x) || !std::isfinite(ep.y) || !std::isfinite(ep.z)) continue;
                float dx = ep.x - pos.x, dy = ep.y - pos.y, dz = ep.z - pos.z;
                if (dx * dx + dy * dy + dz * dz < 2500.f) near = true;
            }
            if (!near) continue;

            g_gameHits.push_back(sec[s].VirtualAddress + off);
            if (g_gameHits.size() >= 24) break;
        }
        if (g_gameHits.size() >= 24) break;
    }
}

// ---------------- globals ----------------
static HMODULE             g_hSelf    = nullptr;
static HWND                g_hwnd     = nullptr;
static std::atomic<bool>   g_running{ false };
static HFONT               g_font     = nullptr;

static Camera              g_cam;
static std::vector<Player> g_players;
static std::wstring        g_status;
static uintptr_t           g_game = 0, g_world = 0, g_local = 0;
static int                 g_entCount = 0, g_candidates = 0, g_saneEnts = 0;
static int                 g_scrW = 0, g_scrH = 0;

static bool Finite(const Vec3& v) {
    return std::isfinite(v.x) && std::isfinite(v.y) && std::isfinite(v.z);
}

static bool WorldToScreen(const Vec3& w, Vec2& out) {
    if (!g_cam.valid || g_scrW < 1 || g_scrH < 1) return false;
    Vec3 d{ w.x - g_cam.pos.x, w.y - g_cam.pos.y, w.z - g_cam.pos.z };
    float x = d.x * g_cam.right.x + d.y * g_cam.right.y + d.z * g_cam.right.z;
    float y = d.x * g_cam.up.x    + d.y * g_cam.up.y    + d.z * g_cam.up.z;
    float z = d.x * g_cam.fwd.x   + d.y * g_cam.fwd.y   + d.z * g_cam.fwd.z;
    if (z <= 0.05f) return false;
    float tanY = tanf(g_cam.fov * 0.5f);
    if (tanY < 1e-6f) return false;
    float tanX = tanY * ((float)g_scrW / (float)g_scrH);
    out.x = (g_scrW * 0.5f) * (1.f + (x / z) / tanX);
    out.y = (g_scrH * 0.5f) * (1.f - (y / z) / tanY);
    return true;
}

// ---------------- chain ----------------
static void Update() {
    g_players.clear();
    g_status.clear();
    g_candidates = 0;
    g_saneEnts   = 0;
    g_cam.valid  = false;

    g_game = Read<uintptr_t>(g_base + g_off.Game);
    if (!g_game) { g_status = L"game null"; return; }

    g_world = Read<uintptr_t>(g_game + g_off.GameWorld);
    if (!g_world) { g_status = L"world null"; return; }

    uintptr_t ctrlWeak = Read<uintptr_t>(g_world + g_off.LocalPlayerController);
    if (!ctrlWeak) { g_status = L"ctrl weak null"; return; }
    uintptr_t ctrl = Read<uintptr_t>(ctrlWeak + g_off.WeakPtr);
    if (!ctrl) { g_status = L"ctrl null"; return; }
    g_local = ctrl - g_off.LocalPlayerDelta;

    uintptr_t pc = Read<uintptr_t>(g_local + g_off.LocalPlayerCamera);
    if (!pc) { g_status = L"camera null"; return; }

    g_cam.pos   = Read<Vec3>(pc + g_off.CameraPosition);
    g_cam.right = Read<Vec3>(pc + g_off.InvertedViewRight);
    g_cam.up    = Read<Vec3>(pc + g_off.InvertedViewUp);
    g_cam.fwd   = Read<Vec3>(pc + g_off.VectorViewForward);
    if (!Finite(g_cam.pos) || !Finite(g_cam.fwd)) { g_status = L"camera garbage"; return; }
    g_cam.valid = true;

    uintptr_t list = Read<uintptr_t>(g_world + g_off.EntityList);
    int count = Read<int>(g_world + g_off.EntityCount);
    g_entCount = count;
    if (!list || count <= 0) { g_status = L"entity list empty"; return; }
    if (count > 8192) count = 8192;

    for (int i = 0; i < count; ++i) {
        uintptr_t ent = Read<uintptr_t>(list + (uintptr_t)i * sizeof(uintptr_t));
        if (!ent || ent < 0x10000 || ent == g_local) continue;

        Vec3 pos = Read<Vec3>(ent + g_off.EntityPosition);
        if (!Finite(pos) || (pos.x == 0.f && pos.y == 0.f && pos.z == 0.f)) continue;
        g_saneEnts++;

        Vec3 d{ pos.x - g_cam.pos.x, pos.y - g_cam.pos.y, pos.z - g_cam.pos.z };
        float dist = sqrtf(d.x * d.x + d.y * d.y + d.z * d.z);
        if (dist > g_maxDist || dist < 0.05f) continue;

        uintptr_t h1 = Read<uintptr_t>(ent + g_off.HealthChain1);
        if (!h1) continue;
        uintptr_t h2 = Read<uintptr_t>(h1 + g_off.HealthChain2);
        if (!h2) continue;
        float hp    = Read<float>(h2 + g_off.Health);
        float hpMax = Read<float>(h2 + g_off.MaxHealth);
        if (!(hpMax > 1.f && hpMax < 10000.f)) continue;
        if (!(hp > 0.f && hp <= hpMax)) continue;
        g_candidates++;

        Player p;
        p.dist = dist; p.hp = hp; p.hpMax = hpMax;
        Vec3 head{ pos.x, pos.y, pos.z + g_aimHeight };
        p.onScreen = WorldToScreen(head, p.head);
        if (p.onScreen) WorldToScreen(pos, p.foot);
        g_players.push_back(p);
    }
}

// ---------------- drawing ----------------
static HFONT Font() {
    if (!g_font)
        g_font = CreateFontW(-14, 0, 0, 0, FW_SEMIBOLD, FALSE, FALSE, FALSE,
                             DEFAULT_CHARSET, OUT_TT_PRECIS, CLIP_DEFAULT_PRECIS,
                             ANTIALIASED_QUALITY, DEFAULT_PITCH | FF_DONTCARE, L"Consolas");
    return g_font;
}

static void Text(HDC dc, int x, int y, const std::wstring& s, COLORREF col) {
    if (s.empty()) return;
    HFONT old = (HFONT)SelectObject(dc, Font());
    SetBkMode(dc, TRANSPARENT);
    SetTextColor(dc, RGB(1, 1, 1));                 // shadow - never pure black
    TextOutW(dc, x + 1, y, s.c_str(), (int)s.size());
    TextOutW(dc, x, y + 1, s.c_str(), (int)s.size());
    SetTextColor(dc, col);
    TextOutW(dc, x, y, s.c_str(), (int)s.size());
    SelectObject(dc, old);
}

static void Box(HDC dc, float x, float y, float w, float h, COLORREF col) {
    HPEN pen = CreatePen(PS_SOLID, 1, col);
    HPEN op  = (HPEN)SelectObject(dc, pen);
    HBRUSH ob = (HBRUSH)SelectObject(dc, GetStockObject(NULL_BRUSH));
    Rectangle(dc, (int)x, (int)y, (int)(x + w), (int)(y + h));
    SelectObject(dc, ob);
    SelectObject(dc, op);
    DeleteObject(pen);
}

static void Fill(HDC dc, float x, float y, float w, float h, COLORREF col) {
    RECT r{ (LONG)x, (LONG)y, (LONG)(x + w), (LONG)(y + h) };
    HBRUSH b = CreateSolidBrush(col);
    ::FillRect(dc, &r, b);
    DeleteObject(b);
}

static void Draw(HDC dc, int w, int h) {
    HBRUSH bg = CreateSolidBrush(RGB(0, 0, 0));      // pure black = transparent
    RECT rc{ 0, 0, w, h };
    FillRect(dc, &rc, bg);
    DeleteObject(bg);

    if (g_espOn && g_cam.valid) {
        for (const auto& p : g_players) {
            if (!p.onScreen) continue;
            float bh = fabsf(p.foot.y - p.head.y);
            if (bh < 3.f) bh = 3.f;
            float bw = bh * 0.55f;
            float bx = (p.head.x + p.foot.x) * 0.5f - bw * 0.5f;
            float by = p.head.y;

            Box(dc, bx, by, bw, bh, RGB(0, 255, 130));

            if (p.hpMax > 0.f) {
                float frac = p.hp / p.hpMax;
                if (frac < 0.f) frac = 0.f;
                if (frac > 1.f) frac = 1.f;
                Fill(dc, bx - 6.f, by, 3.f, bh, RGB(45, 45, 45));
                Fill(dc, bx - 6.f, by + bh * (1.f - frac), 3.f, bh * frac, RGB(0, 255, 130));
            }

            wchar_t nbuf[32];
            swprintf_s(nbuf, L"%dm", (int)p.dist);
            Text(dc, (int)(bx + bw * 0.5f) - 14, (int)(by + bh + 2), nbuf, RGB(205, 205, 205));
        }
    }

    if (g_showDebug) {
        std::vector<std::wstring> lines;
        wchar_t buf[256];

        lines.push_back(L"ESP LOADED");

        swprintf_s(buf, L"base  %llX", (unsigned long long)g_base);
        lines.push_back(buf);
        swprintf_s(buf, L"game  %llX", (unsigned long long)g_game);
        lines.push_back(buf);
        swprintf_s(buf, L"world %llX", (unsigned long long)g_world);
        lines.push_back(buf);
        swprintf_s(buf, L"local %llX", (unsigned long long)g_local);
        lines.push_back(buf);

        swprintf_s(buf, L"ents %d | sane %d | cand %d | players %d",
                   g_entCount, g_saneEnts, g_candidates, (int)g_players.size());
        lines.push_back(buf);

        swprintf_s(buf, L"cam %.1f %.1f %.1f",
                   (double)g_cam.pos.x, (double)g_cam.pos.y, (double)g_cam.pos.z);
        lines.push_back(buf);

        lines.push_back(g_status.empty() ? L"status OK" : g_status);

        swprintf_s(buf, L"Game off = 0x%llX", (unsigned long long)g_off.Game);
        lines.push_back(buf);

        if (!g_gameHits.empty()) {
            swprintf_s(buf, L"HITS %d  first 0x%llX  (F4 = try next)",
                       (int)g_gameHits.size(), (unsigned long long)g_gameHits[0]);
            lines.push_back(buf);
        }

        lines.push_back(L"F1 esp  F2 debug  F3 hunt  F4 apply");

        int y = 8;
        for (size_t i = 0; i < lines.size(); ++i) {
            Text(dc, 10, y, lines[i], RGB(0, 220, 255));
            y += 17;
        }
    }
}

// ---------------- window ----------------
static LRESULT CALLBACK WndProc(HWND h, UINT m, WPARAM wp, LPARAM lp) {
    switch (m) {
        case WM_ERASEBKGND: return 1;
        case WM_PAINT: {
            PAINTSTRUCT ps;
            HDC dc = BeginPaint(h, &ps);
            RECT rc; GetClientRect(h, &rc);
            Draw(dc, rc.right, rc.bottom);
            EndPaint(h, &ps);
            return 0;
        }
        case WM_DESTROY: PostQuitMessage(0); return 0;
    }
    return DefWindowProcW(h, m, wp, lp);
}

static bool CreateOverlay() {
    WNDCLASSEXW wc{};
    wc.cbSize        = sizeof(wc);
    wc.lpfnWndProc   = WndProc;
    wc.hInstance     = g_hSelf;
    wc.hbrBackground = nullptr;
    wc.lpszClassName = L"ArmaEspOverlay";
    if (!RegisterClassExW(&wc)) return false;

    g_hwnd = CreateWindowExW(
        WS_EX_TOPMOST | WS_EX_LAYERED | WS_EX_TRANSPARENT |
        WS_EX_TOOLWINDOW | WS_EX_NOACTIVATE,
        L"ArmaEspOverlay", L"ArmaEsp", WS_POPUP, 0, 0, 200, 200,
        nullptr, nullptr, g_hSelf, nullptr);
    if (!g_hwnd) return false;

    SetLayeredWindowAttributes(g_hwnd, RGB(0, 0, 0), 0, LWA_COLORKEY);
    ShowWindow(g_hwnd, SW_SHOWNOACTIVATE);
    return true;
}

static bool KeyPressed(int vk) {
    static bool state[256] = {};
    bool down = (GetAsyncKeyState(vk) & 0x8000) != 0;
    bool fired = down && !state[vk];
    state[vk] = down;
    return fired;
}

static DWORD WINAPI MainThread(LPVOID) {
    g_base = (uintptr_t)GetModuleHandleW(nullptr);
    if (!CreateOverlay()) return 0;

    MSG msg;
    while (g_running) {
        while (PeekMessageW(&msg, nullptr, 0, 0, PM_REMOVE)) {
            TranslateMessage(&msg);
            DispatchMessageW(&msg);
        }

        HWND game = GetForegroundWindow();
        RECT cr{};
        if (game && game != g_hwnd && GetClientRect(game, &cr) &&
            cr.right > 200 && cr.bottom > 200) {
            POINT tl{ 0, 0 };
            ClientToScreen(game, &tl);
            SetWindowPos(g_hwnd, HWND_TOPMOST, tl.x, tl.y, cr.right, cr.bottom,
                         SWP_NOACTIVATE);
            g_scrW = cr.right;
            g_scrH = cr.bottom;
        }

        if (KeyPressed(VK_F1)) g_espOn     = !g_espOn;
        if (KeyPressed(VK_F2)) g_showDebug = !g_showDebug;
        if (KeyPressed(VK_F3)) HuntGame();
        if (KeyPressed(VK_F4) && !g_gameHits.empty()) {
            static size_t idx = 0;
            g_off.Game = g_gameHits[idx % g_gameHits.size()];
            idx++;
        }

        Update();
        InvalidateRect(g_hwnd, nullptr, FALSE);
        Sleep(1);
    }

    if (g_font) DeleteObject(g_font);
    if (g_hwnd) DestroyWindow(g_hwnd);
    return 0;
}

BOOL APIENTRY DllMain(HMODULE hModule, DWORD reason, LPVOID) {
    if (reason == DLL_PROCESS_ATTACH) {
        DisableThreadLibraryCalls(hModule);
        g_hSelf   = hModule;
        g_running = true;
        HANDLE t = CreateThread(nullptr, 0, MainThread, nullptr, 0, nullptr);
        if (t) CloseHandle(t);
    } else if (reason == DLL_PROCESS_DETACH) {
        g_running = false;
    }
    return TRUE;
}
