// esp_loader.cpp - stage 4: health chain hunt
#define WIN32_LEAN_AND_MEAN
#define NOMINMAX
#include <windows.h>
#include <cstdint>
#include <cstddef>
#include <cstdio>
#include <cwchar>
#include <cmath>
#include <atomic>
#include <string>
#include <vector>

#pragma comment(lib, "gdi32.lib")
#pragma comment(lib, "user32.lib")

// ---------------- config ----------------
static bool  g_espOn      = true;
static bool  g_showDebug  = true;
static bool  g_needHealth = true;
static float g_maxDist    = 800.f;
static float g_aimHeight  = 1.72f;

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

// ---------------- offsets ----------------
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

// ---- stage 5 diagnostics ----
static bool      g_noDist = false;
static float     g_dMin = 1.0e9f, g_dMax = -1.0e9f;
static float     g_dump[3][3] = {};
static uintptr_t g_foundPos = 0;
static int       g_posSpread = 0;
static float     g_posBox = 0.f;
static void RescanEntityPosition();

// ---------------- memory ----------------
static uintptr_t g_base = 0;

static inline bool SafeReadRaw(uintptr_t a, void* dst, size_t n) {
    __try {
        memcpy(dst, reinterpret_cast<const void*>(a), n);
        return true;
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        return false;
    }
}

template <typename T>
static inline T Read(uintptr_t a) {
    if (a < 0x10000 || a > 0x7FFFFFFFFFFFull) return T{};
    T v{};
    if (!SafeReadRaw(a, &v, sizeof(T))) return T{};
    return v;
}

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
static int                 g_distOk = 0, g_h1Ok = 0, g_h2Ok = 0, g_hpOk = 0;
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

// ---------------- health pair test ----------------
static bool HealthPairOk(uintptr_t ent, uintptr_t c1, uintptr_t c2, uintptr_t hpOff,
                         float& hpOut, float& maxOut) {
    uintptr_t h1 = Read<uintptr_t>(ent + c1);
    if (!h1) return false;
    uintptr_t h2 = Read<uintptr_t>(h1 + c2);
    if (!h2) return false;
    float hp    = Read<float>(h2 + hpOff);
    float hpMax = Read<float>(h2 + hpOff - 4);
    if (!(hpMax > 0.1f && hpMax < 1000000.f)) return false;
    if (!(hp > 0.f && hp <= hpMax * 1.05f)) return false;
    hpOut = hp; maxOut = hpMax;
    return true;
}

// ---------------- hunter ----------------
struct GameHit {
    uintptr_t game;
    uintptr_t listOff;
    uintptr_t posOff;
    uintptr_t cntOff;
};

static std::vector<GameHit> g_gameHits;
static int g_hScan = 0, g_hPtr = 0, g_hWorld = 0, g_hCtrl = 0, g_hCam = 0, g_hEnt = 0;
static uintptr_t g_fC1 = 0, g_fC2 = 0, g_fHp = 0;

static bool SearchEntityOffsets(uintptr_t world, const Vec3& cam,
                                uintptr_t& oList, uintptr_t& oPos, uintptr_t& oCnt) {
    uintptr_t bestList = 0, bestPos = 0;
    int bestSane = 0;

    for (uintptr_t lo = 8; lo < 0x400; lo += 8) {
        uintptr_t list = Read<uintptr_t>(world + lo);
        if (!Readable(list, 8)) continue;

        for (uintptr_t po = 0; po < 0x200; po += 4) {
            int sane = 0;
            float minD = 1.0e18f, sumD = 0.f;

            for (int i = 0; i < 384; ++i) {
                uintptr_t e = Read<uintptr_t>(list + (uintptr_t)i * sizeof(uintptr_t));
                if (!Readable(e, 16)) break;
                Vec3 p = Read<Vec3>(e + po);
                if (!std::isfinite(p.x) || !std::isfinite(p.y) || !std::isfinite(p.z)) continue;
                if (p.x == 0.f && p.y == 0.f && p.z == 0.f) continue;
                float dx = p.x - cam.x, dy = p.y - cam.y, dz = p.z - cam.z;
                float dd = sqrtf(dx * dx + dy * dy + dz * dz);
                if (dd < minD) minD = dd;
                sumD += dd;
                sane++;
            }
            if (sane < 8) continue;
            if (sane > bestSane) { bestSane = sane; bestList = lo; bestPos = po; }

            float avgD = sumD / (float)sane;
            if (!(minD < 50.f || minD < 0.05f * avgD)) continue;

            oList = lo; oPos = po; oCnt = 0;
            for (uintptr_t co = 8; co < 0x400; co += 4) {
                int c = Read<int>(world + co);
                if (c >= sane && c <= 100000) { oCnt = co; break; }
            }
            return true;
        }
    }
    if (bestSane >= 32) {
        oList = bestList; oPos = bestPos; oCnt = 0;
        for (uintptr_t co = 8; co < 0x400; co += 4) {
            int c = Read<int>(world + co);
            if (c >= bestSane && c <= 100000) { oCnt = co; break; }
        }
        return true;
    }
    return false;
}

// Search the health chain. Characters share a max health value, so we require
// several hits to agree on it - that kills the coincidences.
static void FindHealthOffsets() {
    g_fC1 = g_fC2 = g_fHp = 0;
    if (!g_world || !g_cam.valid) return;

    uintptr_t list = Read<uintptr_t>(g_world + g_off.EntityList);
    int count = Read<int>(g_world + g_off.EntityCount);
    if (!list || count <= 0) return;
    if (count > 4096) count = 4096;

    std::vector<uintptr_t> sample;
    for (int i = 0; i < count && sample.size() < 64; ++i) {
        uintptr_t e = Read<uintptr_t>(list + (uintptr_t)i * sizeof(uintptr_t));
        if (!e || e < 0x10000) continue;
        Vec3 p = Read<Vec3>(e + g_off.EntityPosition);
        if (!std::isfinite(p.x) || !std::isfinite(p.y) || !std::isfinite(p.z)) continue;
        float dx = p.x - g_cam.pos.x, dy = p.y - g_cam.pos.y, dz = p.z - g_cam.pos.z;
        if (sqrtf(dx * dx + dy * dy + dz * dz) > g_maxDist) continue;
        sample.push_back(e);
    }
    if (sample.size() < 4) return;

    for (uintptr_t c1 = 0; c1 < 0x300; c1 += 8) {
        for (uintptr_t c2 = 0; c2 < 0x200; c2 += 8) {
            for (uintptr_t hp = 4; hp < 0x80; hp += 4) {
                int good = 0, sameMax = 0;
                float firstMax = 0.f;
                for (size_t i = 0; i < sample.size(); ++i) {
                    float a, b;
                    if (!HealthPairOk(sample[i], c1, c2, hp, a, b)) continue;
                    good++;
                    if (firstMax == 0.f) firstMax = b;
                    else if (fabsf(b - firstMax) < 0.02f * firstMax) sameMax++;
                }
                if (good >= 4 && sameMax >= 3) {
                    g_fC1 = c1; g_fC2 = c2; g_fHp = hp;
                    g_off.HealthChain1 = c1;
                    g_off.HealthChain2 = c2;
                    g_off.Health    = hp;
                    g_off.MaxHealth = hp - 4;
                    return;
                }
            }
        }
    }
}

static void HuntGame() {
    g_gameHits.clear();
    g_hScan = g_hPtr = g_hWorld = g_hCtrl = g_hCam = g_hEnt = 0;
    if (!g_base) return;

    auto dos = reinterpret_cast<PIMAGE_DOS_HEADER>(g_base);
    if (dos->e_magic != IMAGE_DOS_SIGNATURE) return;
    auto nt = reinterpret_cast<PIMAGE_NT_HEADERS>(g_base + dos->e_lfanew);

    auto sec = reinterpret_cast<PIMAGE_SECTION_HEADER>(
        reinterpret_cast<uintptr_t>(&nt->OptionalHeader) +
        nt->FileHeader.SizeOfOptionalHeader);

    for (int s = 0; s < (int)nt->FileHeader.NumberOfSections; ++s) {
        if (!(sec[s].Characteristics & IMAGE_SCN_MEM_WRITE)) continue;
        size_t vsec = sec[s].Misc.VirtualSize;
        if (vsec < 8) continue;
        uintptr_t start = g_base + sec[s].VirtualAddress;

        for (size_t off = 0; off + sizeof(uintptr_t) <= vsec; off += sizeof(uintptr_t)) {
            g_hScan++;
            uintptr_t v = Read<uintptr_t>(start + off);
            if (!Readable(v, 8)) continue;
            g_hPtr++;

            uintptr_t w = Read<uintptr_t>(v + g_off.GameWorld);
            if (!Readable(w, 8)) continue;
            g_hWorld++;

            uintptr_t cw = Read<uintptr_t>(w + g_off.LocalPlayerController);
            if (!Readable(cw, 8)) continue;
            g_hCtrl++;

            uintptr_t c = Read<uintptr_t>(cw + g_off.WeakPtr);
            if (!Readable(c, 8)) continue;

            uintptr_t pc = Read<uintptr_t>((c - g_off.LocalPlayerDelta) + g_off.LocalPlayerCamera);
            if (!Readable(pc, 12)) continue;

            Vec3 pos = Read<Vec3>(pc + g_off.CameraPosition);
            Vec3 fwd = Read<Vec3>(pc + g_off.VectorViewForward);
            if (!std::isfinite(pos.x) || !std::isfinite(pos.y) || !std::isfinite(pos.z)) continue;
            if (!std::isfinite(fwd.x) || !std::isfinite(fwd.y) || !std::isfinite(fwd.z)) continue;
            float mag = sqrtf(pos.x * pos.x + pos.y * pos.y + pos.z * pos.z);
            if (mag < 1.f || mag > 1.0e7f) continue;
            g_hCam++;

            uintptr_t oList = 0, oPos = 0, oCnt = 0;
            if (!SearchEntityOffsets(w, pos, oList, oPos, oCnt)) continue;
            g_hEnt++;

            GameHit hit{ sec[s].VirtualAddress + off, oList, oPos, oCnt };
            g_gameHits.push_back(hit);
            if (g_gameHits.size() >= 8) break;
        }
        if (g_gameHits.size() >= 8) break;
    }
}

// ---------------- chain ----------------
static void Update() {
    g_players.clear();
    g_status.clear();
    g_candidates = 0;
    g_saneEnts = g_distOk = g_h1Ok = g_h2Ok = g_hpOk = 0;
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
        if (dist < g_dMin) g_dMin = dist;
        if (dist > g_dMax) g_dMax = dist;
        if (g_saneEnts >= 1 && g_saneEnts <= 3) {
            int k = g_saneEnts - 1;
            g_dump[k][0] = pos.x; g_dump[k][1] = pos.y; g_dump[k][2] = pos.z;
        }
        if (!g_noDist && (dist > g_maxDist || dist < 0.05f)) continue;
        g_distOk++;

        float hp = 0.f, hpMax = 0.f;
        if (g_needHealth) {
            uintptr_t h1 = Read<uintptr_t>(ent + g_off.HealthChain1);
            if (!h1) continue;
            g_h1Ok++;
            uintptr_t h2 = Read<uintptr_t>(h1 + g_off.HealthChain2);
            if (!h2) continue;
            g_h2Ok++;
            hp    = Read<float>(h2 + g_off.Health);
            hpMax = Read<float>(h2 + g_off.MaxHealth);
            if (!(hpMax > 0.1f && hpMax < 1000000.f)) continue;
            if (!(hp > 0.f && hp <= hpMax * 1.05f)) continue;
            g_hpOk++;
        } else {
            hpMax = 100.f; hp = 100.f;
        }
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
    SetTextColor(dc, RGB(1, 1, 1));
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
    HBRUSH bg = CreateSolidBrush(RGB(0, 0, 0));
    RECT rc{ 0, 0, w, h };
    FillRect(dc, &rc, bg);
    DeleteObject(bg);

    if (g_espOn && g_cam.valid) {
        for (size_t i = 0; i < g_players.size(); ++i) {
            const Player& p = g_players[i];
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

        swprintf_s(buf, L"base  %llX", (unsigned long long)g_base);   lines.push_back(buf);
        swprintf_s(buf, L"game  %llX", (unsigned long long)g_game);   lines.push_back(buf);
        swprintf_s(buf, L"world %llX", (unsigned long long)g_world);  lines.push_back(buf);
        swprintf_s(buf, L"local %llX", (unsigned long long)g_local);  lines.push_back(buf);

        swprintf_s(buf, L"ents %d | sane %d | dist %d | h1 %d | h2 %d | hp %d | cand %d | players %d",
                   g_entCount, g_saneEnts, g_distOk, g_h1Ok, g_h2Ok, g_hpOk,
                   g_candidates, (int)g_players.size());
        lines.push_back(buf);

        swprintf_s(buf, L"cam %.1f %.1f %.1f  maxD %.0f  noDist %d",
                   (double)g_cam.pos.x, (double)g_cam.pos.y, (double)g_cam.pos.z,
                   (double)g_maxDist, (int)g_noDist);
        lines.push_back(buf);

        swprintf_s(buf, L"dmin %.1f  dmax %.1f", (double)g_dMin, (double)g_dMax);
        lines.push_back(buf);

        swprintf_s(buf, L"e0 %.1f %.1f %.1f", (double)g_dump[0][0], (double)g_dump[0][1], (double)g_dump[0][2]);
        lines.push_back(buf);
        swprintf_s(buf, L"e1 %.1f %.1f %.1f", (double)g_dump[1][0], (double)g_dump[1][1], (double)g_dump[1][2]);
        lines.push_back(buf);
        swprintf_s(buf, L"e2 %.1f %.1f %.1f", (double)g_dump[2][0], (double)g_dump[2][1], (double)g_dump[2][2]);
        lines.push_back(buf);

        swprintf_s(buf, L"rescan 0x%llX spread %d box %.1f",
                   (unsigned long long)g_foundPos, g_posSpread, (double)g_posBox);
        lines.push_back(buf);

        g_dMin = 1.0e9f; g_dMax = -1.0e9f;

        lines.push_back(g_status.empty() ? L"status OK" : g_status);

        swprintf_s(buf, L"G 0x%llX L 0x%llX P 0x%llX C 0x%llX  hc1 0x%llX hc2 0x%llX hp 0x%llX",
                   (unsigned long long)g_off.Game, (unsigned long long)g_off.EntityList,
                   (unsigned long long)g_off.EntityPosition, (unsigned long long)g_off.EntityCount,
                   (unsigned long long)g_off.HealthChain1, (unsigned long long)g_off.HealthChain2,
                   (unsigned long long)g_off.Health);
        lines.push_back(buf);

        swprintf_s(buf, L"hunt scan %d ptr %d wld %d ctl %d cam %d ent %d",
                   g_hScan, g_hPtr, g_hWorld, g_hCtrl, g_hCam, g_hEnt);
        lines.push_back(buf);

        if (g_fHp) {
            swprintf_s(buf, L"HEALTH FOUND c1 0x%llX c2 0x%llX hp 0x%llX",
                       (unsigned long long)g_fC1, (unsigned long long)g_fC2,
                       (unsigned long long)g_fHp);
            lines.push_back(buf);
        }

        lines.push_back(L"F1 esp  F2 debug  F3 hunt  F4 apply  F5 health F6 find-health F5 noHealth  F7 noDist  F8 rescan pos");
        

        int y = 8;
        for (size_t i = 0; i < lines.size(); ++i) {
            Text(dc, 10, y, lines[i], RGB(0, 220, 255));
            y += 17;
        }
    }
}

// Re-search ONLY the entity-position offset, using the entity list we already
// trust. Real positions are all distinct from each other and at least one of
// them sits near the camera; garbage (pointers / rotation data read as floats)
// is neither.
static void RescanEntityPosition() {
    g_foundPos = 0; g_posSpread = 0; g_posBox = 0.f;
    if (!g_world) return;

    uintptr_t list = Read<uintptr_t>(g_world + g_off.EntityList);
    int count = Read<int>(g_world + g_off.EntityCount);
    if (!list || count <= 0) return;
    if (count > 512) count = 512;

    uintptr_t ents[192];
    int n = 0;
    for (int i = 0; i < count && n < 192; ++i) {
        uintptr_t e = Read<uintptr_t>(list + (uintptr_t)i * sizeof(uintptr_t));
        if (!e || e < 0x10000) continue;
        ents[n++] = e;
    }
    if (n < 8) return;

    float camMag = sqrtf(g_cam.pos.x * g_cam.pos.x + g_cam.pos.y * g_cam.pos.y + g_cam.pos.z * g_cam.pos.z);
    float nearLimit = 100.f;
    if (0.05f * camMag > nearLimit) nearLimit = 0.05f * camMag;

    bool found = false;
    uintptr_t bestOff = 0;
    int bestSpread = -1;
    float bestBox = 0.f;

    for (uintptr_t po = 0; po < 0x400; po += 4) {
        Vec3 first{}; bool haveFirst = false;
        float minD = 1.0e30f;
        float mn[3] = { 1.0e30f, 1.0e30f, 1.0e30f };
        float mx[3] = { -1.0e30f, -1.0e30f, -1.0e30f };
        int finite = 0, spread = 0;

        for (int i = 0; i < n; ++i) {
            Vec3 p = Read<Vec3>(ents[i] + po);
            if (!std::isfinite(p.x) || !std::isfinite(p.y) || !std::isfinite(p.z)) continue;
            if (p.x == 0.f && p.y == 0.f && p.z == 0.f) continue;
            finite++;
            if (p.x < mn[0]) mn[0] = p.x;
            if (p.y < mn[1]) mn[1] = p.y;
            if (p.z < mn[2]) mn[2] = p.z;
            if (p.x > mx[0]) mx[0] = p.x;
            if (p.y > mx[1]) mx[1] = p.y;
            if (p.z > mx[2]) mx[2] = p.z;
            float dx = p.x - g_cam.pos.x, dy = p.y - g_cam.pos.y, dz = p.z - g_cam.pos.z;
            float dd = sqrtf(dx * dx + dy * dy + dz * dz);
            if (dd < minD) minD = dd;
            if (!haveFirst) { first = p; haveFirst = true; }
            else if (fabsf(p.x - first.x) > 0.01f || fabsf(p.y - first.y) > 0.01f ||
                     fabsf(p.z - first.z) > 0.01f)
                spread++;
        }

        if (finite < n / 2) continue;
        if (minD > nearLimit) continue;

        float bx = mx[0] - mn[0], by = mx[1] - mn[1], bz = mx[2] - mn[2];
        float box = sqrtf(bx * bx + by * by + bz * bz);
        if (!(box > 0.5f && box < 1.0e7f)) continue;

        if (spread > bestSpread) { bestSpread = spread; bestOff = po; bestBox = box; found = true; }
    }

    if (!found) return;
    g_foundPos  = bestOff;
    g_posSpread = bestSpread;
    g_posBox    = bestBox;
    g_off.EntityPosition = bestOff;
}
// ---------------- window ----------------
static LRESULT CALLBACK WndProc(HWND h, UINT m, WPARAM wp, LPARAM lp) {
    switch (m) {
        case WM_ERASEBKGND: return 1;
        case WM_PAINT: {
            PAINTSTRUCT ps;
            HDC dc = BeginPaint(h, &ps);
            RECT cr; GetClientRect(h, &cr);
            Draw(dc, cr.right, cr.bottom);
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

        if (KeyPressed(VK_F1)) g_espOn      = !g_espOn;
        if (KeyPressed(VK_F2)) g_showDebug  = !g_showDebug;
        if (KeyPressed(VK_F5)) g_needHealth = !g_needHealth;
        if (KeyPressed(VK_F3)) HuntGame();
        if (KeyPressed(VK_F6)) FindHealthOffsets();
        if (KeyPressed(VK_F7)) g_noDist = !g_noDist;
        if (KeyPressed(VK_F8)) RescanEntityPosition();
        if (KeyPressed(VK_F4) && !g_gameHits.empty()) {
            static size_t idx = 0;
            const GameHit& hh = g_gameHits[idx % g_gameHits.size()];
            g_off.Game           = hh.game;
            if (hh.listOff) g_off.EntityList     = hh.listOff;
            if (hh.posOff)  g_off.EntityPosition = hh.posOff;
            if (hh.cntOff)  g_off.EntityCount    = hh.cntOff;
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
