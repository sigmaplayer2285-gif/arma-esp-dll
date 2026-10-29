// esp_loader.cpp - stage 9: dots + camera position from local entity
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#ifndef NOMINMAX
#define NOMINMAX
#endif
#ifndef WDA_EXCLUDEFROMCAPTURE
#define WDA_EXCLUDEFROMCAPTURE 0x00000011
#endif

#include <windows.h>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <cmath>
#include <cwchar>
#include <atomic>
#include <string>
#include <vector>
#include <algorithm>

#pragma comment(lib, "gdi32.lib")
#pragma comment(lib, "user32.lib")

// ---------------- config ----------------
static bool  g_espOn     = true;
static bool  g_showDebug = true;
static float g_maxDist   = 400.f;
static float g_aimHeight = 1.72f;

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

// ---------------- math ----------------
struct Vec2 { float x = 0.f, y = 0.f; };
struct Vec3 { float x = 0.f, y = 0.f, z = 0.f; };

struct Camera {
    Vec3 pos{};
    Vec3 right{};
    Vec3 up{};
    Vec3 fwd{};
    bool valid = false;
};

struct Player {
    float dist = 0.f;
    float hp = 0.f;
    float hpMax = 0.f;
    Vec2  head{};
    bool  onScreen = false;
};

// ---------------- memory ----------------
static uintptr_t g_base = 0;

static bool SafeReadRaw(uintptr_t addr, void* dst, size_t size) {
    __try {
        memcpy(dst, reinterpret_cast<const void*>(addr), size);
        return true;
    }
    __except (EXCEPTION_EXECUTE_HANDLER) {
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

static bool Finite(const Vec3& v) {
    return std::isfinite(v.x) && std::isfinite(v.y) && std::isfinite(v.z);
}

static bool SolidPos(const Vec3& p) {
    if (!Finite(p)) return false;
    if (p.x == 0.f && p.y == 0.f && p.z == 0.f) return false;
    if (fabsf(p.x) > 1.0e7f || fabsf(p.y) > 1.0e7f || fabsf(p.z) > 1.0e7f) return false;
    return true;
}

// ---------------- state ----------------
static HWND    g_hwnd  = nullptr;
static HDC     g_dc    = nullptr;
static HFONT   g_font  = nullptr;
static int     g_w     = 0;
static int     g_h     = 0;
static HMODULE g_hSelf = nullptr;
static std::atomic<bool> g_running{ false };

static uintptr_t g_game = 0, g_world = 0, g_local = 0;
static uintptr_t g_lpc = 0, g_weak = 0, g_delta = 0, g_pc = 0;
static uintptr_t g_localEnt = 0;

static Camera    g_cam;
static std::vector<Player> g_players;
static int       g_entCount = 0, g_saneEnts = 0, g_candidates = 0;
static int       g_distOk = 0, g_h1Ok = 0, g_h2Ok = 0, g_hpOk = 0;
static std::wstring g_status;
static bool      g_needHealth = false;

static bool      g_noDist     = false;
static float     g_dMin       = 1.0e9f;
static float     g_dMax       = -1.0e9f;
static float     g_dump[3][3] = {};
static uintptr_t g_foundPos   = 0;
static int       g_posSpread  = 0;
static float     g_posBox     = 0.f;
static uintptr_t g_camRight   = 0;

struct CamCand {
    uintptr_t obj;
    uintptr_t basis;
    uintptr_t stride;
    uintptr_t posOff;
    float     mag;
};
static std::vector<CamCand> g_camCands;

static void RescanEntityPosition();
static void FixCamera();

// ---------------- hunter ----------------
struct GameHit {
    uintptr_t game;
    uintptr_t listOff;
    uintptr_t posOff;
    uintptr_t cntOff;
};

static std::vector<GameHit> g_gameHits;
static int g_hScan = 0, g_hPtr = 0, g_hWorld = 0, g_hCtrl = 0, g_hCam = 0, g_hEnt = 0;

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

            for (int i = 0; i < 256; ++i) {
                uintptr_t e = Read<uintptr_t>(list + (uintptr_t)i * sizeof(uintptr_t));
                if (!Readable(e, 16)) break;
                Vec3 p = Read<Vec3>(e + po);
                if (!SolidPos(p)) continue;
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

static void HuntGame() {
    g_gameHits.clear();
    g_hScan = g_hPtr = g_hWorld = g_hCtrl = g_hCam = g_hEnt = 0;
    if (!g_base) return;

    auto dos = reinterpret_cast<PIMAGE_DOS_HEADER>(g_base);
    if (dos->e_magic != IMAGE_DOS_SIGNATURE) return;
    auto nt = reinterpret_cast<PIMAGE_NT_HEADERS>(g_base + dos->e_lfanew);
    if (nt->Signature != IMAGE_NT_SIGNATURE) return;

    auto sec = reinterpret_cast<PIMAGE_SECTION_HEADER>(
        reinterpret_cast<uintptr_t>(&nt->OptionalHeader) + nt->FileHeader.SizeOfOptionalHeader);

    for (int s = 0; s < (int)nt->FileHeader.NumberOfSections; ++s) {
        if (!(sec[s].Characteristics & IMAGE_SCN_MEM_WRITE)) continue;
        size_t vsec = sec[s].Misc.VirtualSize;
        if (vsec < 8) continue;
        uintptr_t start = g_base + sec[s].VirtualAddress;

        for (uintptr_t off = 0; off + 8 < vsec; off += 8) {
            g_hScan++;
            uintptr_t p = start + off;
            if (!Readable(p, 8)) continue;

            uintptr_t game = Read<uintptr_t>(p);
            if (!game || game < 0x10000) continue;
            g_hPtr++;

            uintptr_t world = Read<uintptr_t>(game + g_off.GameWorld);
            if (!world || world < 0x10000 || !Readable(world, 0x200)) continue;
            g_hWorld++;

            uintptr_t lpc = Read<uintptr_t>(game + g_off.LocalPlayerController);
            if (!lpc || lpc < 0x10000) continue;
            uintptr_t weak = Read<uintptr_t>(lpc + g_off.WeakPtr);
            if (!weak || weak < 0x10000) continue;
            uintptr_t delta = Read<uintptr_t>(weak + g_off.LocalPlayerDelta);
            if (!delta || delta < 0x10000) continue;
            uintptr_t pc = Read<uintptr_t>(delta + g_off.LocalPlayerCamera);
            if (!pc || pc < 0x10000) continue;
            g_hCtrl++;

            Vec3 pos = Read<Vec3>(pc + g_off.CameraPosition);
            if (!SolidPos(pos)) continue;
            float mag = sqrtf(pos.x * pos.x + pos.y * pos.y + pos.z * pos.z);
            if (mag < 1.f || mag > 1.0e7f) continue;
            g_hCam++;

            uintptr_t oList = 0, oPos = 0, oCnt = 0;
            if (SearchEntityOffsets(world, pos, oList, oPos, oCnt)) {
                g_hEnt++;
                GameHit hit{ sec[s].VirtualAddress + off, oList, oPos, oCnt };
                g_gameHits.push_back(hit);
                if (g_gameHits.size() >= 8) break;
            }
        }
        if (g_gameHits.size() >= 8) break;
    }
}

// ---------------- screen ----------------
static bool WorldToScreen(const Vec3& w, Vec2& out) {
    if (!g_cam.valid) return false;
    Vec3 d{ w.x - g_cam.pos.x, w.y - g_cam.pos.y, w.z - g_cam.pos.z };

    float x = d.x * g_cam.right.x + d.y * g_cam.right.y + d.z * g_cam.right.z;
    float y = d.x * g_cam.up.x    + d.y * g_cam.up.y    + d.z * g_cam.up.z;
    float z = d.x * g_cam.fwd.x   + d.y * g_cam.fwd.y   + d.z * g_cam.fwd.z;
    if (z <= 0.05f) return false;

    float tanY = tanf(1.15f * 0.5f);
    if (tanY < 1e-6f) return false;
    float tanX = tanY * ((float)g_w / (float)g_h);

    out.x = (g_w * 0.5f) * (1.f + (x / z) / tanX);
    out.y = (g_h * 0.5f) * (1.f - (y / z) / tanY);
    return true;
}

// ---------------- update ----------------
static void Update() {
    g_players.clear();
    g_entCount = g_saneEnts = g_candidates = 0;
    g_distOk = g_h1Ok = g_h2Ok = g_hpOk = 0;
    g_status.clear();
    g_cam.valid = false;
    g_game = g_world = g_local = 0;
    g_lpc = g_weak = g_delta = g_pc = 0;

    if (!g_base) { g_status = L"base null"; return; }

    uintptr_t game = Read<uintptr_t>(g_base + g_off.Game);
    if (!game) { g_status = L"game null"; return; }
    g_game = game;

    uintptr_t world = Read<uintptr_t>(game + g_off.GameWorld);
    if (!world) { g_status = L"world null"; return; }
    g_world = world;

    uintptr_t lpc = Read<uintptr_t>(game + g_off.LocalPlayerController);
    if (!lpc) { g_status = L"controller null"; return; }
    g_lpc = lpc;

    uintptr_t weak = Read<uintptr_t>(lpc + g_off.WeakPtr);
    if (!weak) { g_status = L"weak null"; return; }
    g_weak = weak;

    uintptr_t delta = Read<uintptr_t>(weak + g_off.LocalPlayerDelta);
    if (!delta) { g_status = L"delta null"; return; }
    g_delta = delta;

    uintptr_t pc = Read<uintptr_t>(delta + g_off.LocalPlayerCamera);
    if (!pc) { g_status = L"camera null"; return; }
    g_local = pc;
    g_pc = pc;

    g_cam.pos   = Read<Vec3>(pc + g_off.CameraPosition);
    g_cam.right = Read<Vec3>(pc + g_off.InvertedViewRight);
    g_cam.up    = Read<Vec3>(pc + g_off.InvertedViewUp);
    g_cam.fwd   = Read<Vec3>(pc + g_off.VectorViewForward);
    if (!Finite(g_cam.right) || !Finite(g_cam.fwd)) { g_status = L"camera garbage"; return; }

    // The camera position is not stored in this object. Fall back to the local
    // entity's own position, which is the same place to within a metre.
    if (!SolidPos(g_cam.pos) && g_localEnt) {
        Vec3 lp = Read<Vec3>(g_localEnt + g_off.EntityPosition);
        if (SolidPos(lp)) {
            g_cam.pos = lp;
            g_cam.pos.z += g_aimHeight;
        }
    }
    if (!SolidPos(g_cam.pos)) { g_status = L"no camera position"; return; }
    g_cam.valid = true;

    uintptr_t list = Read<uintptr_t>(world + g_off.EntityList);
    int count = Read<int>(world + g_off.EntityCount);
    g_entCount = count;
    if (!list || count <= 0) { g_status = L"entity list empty"; return; }
    if (count > 8192) count = 8192;

    for (int i = 0; i < count; ++i) {
        uintptr_t ent = Read<uintptr_t>(list + (uintptr_t)i * sizeof(uintptr_t));
        if (!ent || ent < 0x10000) continue;

        Vec3 pos = Read<Vec3>(ent + g_off.EntityPosition);
        if (!SolidPos(pos)) continue;
        g_saneEnts++;

        Vec3 d{ pos.x - g_cam.pos.x, pos.y - g_cam.pos.y, pos.z - g_cam.pos.z };
        float dist = sqrtf(d.x * d.x + d.y * d.y + d.z * d.z);
        if (dist < g_dMin) g_dMin = dist;
        if (dist > g_dMax) g_dMax = dist;
        if (g_saneEnts >= 1 && g_saneEnts <= 3) {
            int k = g_saneEnts - 1;
            g_dump[k][0] = pos.x;
            g_dump[k][1] = pos.y;
            g_dump[k][2] = pos.z;
        }
        if (!g_noDist && (dist > g_maxDist || dist < 0.5f)) continue;
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
            if (!(hpMax > 0.1f && hpMax < 1.0e6f)) continue;
            if (!(hp > 0.f && hp <= hpMax * 1.05f)) continue;
            g_hpOk++;
        }
        g_candidates++;

        Player p;
        p.dist  = dist;
        p.hp    = hp;
        p.hpMax = hpMax;
        Vec3 head{ pos.x, pos.y, pos.z + g_aimHeight };
        p.onScreen = WorldToScreen(head, p.head);
        g_players.push_back(p);
    }

    std::sort(g_players.begin(), g_players.end(),
              [](const Player& a, const Player& b) { return a.dist < b.dist; });
    if (g_players.size() > 200) g_players.resize(200);
}

// ---------------- local entity ----------------
static void FindLocalEntity() {
    g_localEnt = 0;
    if (!g_pc || !g_world) return;

    uintptr_t list = Read<uintptr_t>(g_world + g_off.EntityList);
    int count = Read<int>(g_world + g_off.EntityCount);
    if (!list || count <= 0) return;
    if (count > 4096) count = 4096;

    std::vector<uintptr_t> ents;
    ents.reserve((size_t)count);
    for (int i = 0; i < count; ++i) {
        uintptr_t e = Read<uintptr_t>(list + (uintptr_t)i * sizeof(uintptr_t));
        if (!e || e < 0x10000) continue;
        ents.push_back(e);
    }
    if (ents.empty()) return;

    // The controller holds a reference to the local player's own entity.
    for (uintptr_t o = 0; o < 0x1000; o += 8) {
        uintptr_t v = Read<uintptr_t>(g_pc + o);
        if (!v || v < 0x10000) continue;
        for (size_t i = 0; i < ents.size(); ++i) {
            if (ents[i] == v) { g_localEnt = v; return; }
        }
    }
}

// ---------------- position rescan ----------------
static void RescanEntityPosition() {
    g_foundPos = 0;
    g_posSpread = 0;
    g_posBox = 0.f;
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

    uintptr_t bestOff = 0;
    int bestSpread = -1;
    float bestBox = 0.f;

    for (uintptr_t po = 0; po < 0x400; po += 4) {
        Vec3 first{};
        bool haveFirst = false;
        float mn[3] = { 1.0e30f, 1.0e30f, 1.0e30f };
        float mx[3] = { -1.0e30f, -1.0e30f, -1.0e30f };
        int finite = 0, spread = 0;

        for (int i = 0; i < n; ++i) {
            Vec3 p = Read<Vec3>(ents[i] + po);
            if (!SolidPos(p)) continue;
            finite++;

            if (p.x < mn[0]) mn[0] = p.x;
            if (p.y < mn[1]) mn[1] = p.y;
            if (p.z < mn[2]) mn[2] = p.z;
            if (p.x > mx[0]) mx[0] = p.x;
            if (p.y > mx[1]) mx[1] = p.y;
            if (p.z > mx[2]) mx[2] = p.z;

            if (!haveFirst) { first = p; haveFirst = true; }
            else if (fabsf(p.x - first.x) > 0.01f || fabsf(p.y - first.y) > 0.01f ||
                     fabsf(p.z - first.z) > 0.01f)
                spread++;
        }

        if (finite < n / 2) continue;

        float bx = mx[0] - mn[0], by = mx[1] - mn[1], bz = mx[2] - mn[2];
        float box = sqrtf(bx * bx + by * by + bz * bz);
        if (!(box > 20.f && box < 1.0e7f)) continue;

        if (spread > bestSpread) {
            bestSpread = spread;
            bestOff = po;
            bestBox = box;
        }
    }

    if (bestSpread < 0) return;
    g_foundPos = bestOff;
    g_posSpread = bestSpread;
    g_posBox = bestBox;
    g_off.EntityPosition = bestOff;
}

// ---------------- camera recovery ----------------
static bool UnitVec(const Vec3& v) {
    float m = v.x * v.x + v.y * v.y + v.z * v.z;
    return m > 0.90f && m < 1.10f;
}

static float Dot3(const Vec3& a, const Vec3& b) {
    return a.x * b.x + a.y * b.y + a.z * b.z;
}

static void ScanBasis(uintptr_t obj) {
    if (!obj || obj < 0x10000) return;

    for (uintptr_t o = 0; o < 0x800; o += 4) {
        for (int s = 0; s < 2; ++s) {
            const uintptr_t stride = s ? 0x10 : 0x0C;

            Vec3 r = Read<Vec3>(obj + o);
            Vec3 u = Read<Vec3>(obj + o + stride);
            Vec3 f = Read<Vec3>(obj + o + stride * 2);
            if (!UnitVec(r) || !UnitVec(u) || !UnitVec(f)) continue;
            if (fabsf(Dot3(r, u)) > 0.15f || fabsf(Dot3(r, f)) > 0.15f ||
                fabsf(Dot3(u, f)) > 0.15f) continue;

            uintptr_t posOffs[3];
            int np = 0;
            if (o >= 0x18) posOffs[np++] = o - 0x18;
            posOffs[np++] = o + stride * 3;
            posOffs[np++] = o + stride * 3 + 0x10;

            for (int k = 0; k < np; ++k) {
                Vec3 p = Read<Vec3>(obj + posOffs[k]);
                if (!SolidPos(p)) continue;

                int solid = 0;
                if (fabsf(p.x) >= 1.f) solid++;
                if (fabsf(p.y) >= 1.f) solid++;
                if (fabsf(p.z) >= 1.f) solid++;
                if (solid < 2) continue;

                float m = sqrtf(p.x * p.x + p.y * p.y + p.z * p.z);
                if (m < 1.f || m > 1.0e6f) continue;

                g_camCands.push_back(CamCand{ obj, o, stride, posOffs[k], m });
                break;
            }
            if (g_camCands.size() > 512) return;
        }
    }
}

static void FixCamera() {
    g_camCands.clear();
    g_camRight = 0;

    FindLocalEntity();
    RescanEntityPosition();

    uintptr_t roots[6] = { g_pc, g_delta, g_weak, g_lpc, g_world, g_game };
    for (int i = 0; i < 6; ++i) {
        if (!roots[i]) continue;
        ScanBasis(roots[i]);
        int kids = 0;
        for (uintptr_t o = 0; o < 0x800 && kids < 128; o += 8) {
            uintptr_t sub = Read<uintptr_t>(roots[i] + o);
            if (!sub || sub < 0x10000) continue;
            if (!Readable(sub, 0x100)) continue;
            kids++;
            ScanBasis(sub);
        }
    }
    if (g_camCands.empty()) return;

    const CamCand* best = &g_camCands[0];
    for (size_t i = 1; i < g_camCands.size(); ++i)
        if (g_camCands[i].mag > best->mag) best = &g_camCands[i];

    g_off.CameraPosition    = best->posOff;
    g_off.InvertedViewRight = best->basis;
    g_off.InvertedViewUp    = best->basis + best->stride;
    g_off.VectorViewForward = best->basis + best->stride * 2;
    g_camRight = best->basis;

    g_cam.right = Read<Vec3>(best->obj + best->basis);
    g_cam.up    = Read<Vec3>(best->obj + best->basis + best->stride);
    g_cam.fwd   = Read<Vec3>(best->obj + best->basis + best->stride * 2);

    if (g_localEnt) {
        Vec3 lp = Read<Vec3>(g_localEnt + g_off.EntityPosition);
        if (SolidPos(lp)) {
            g_cam.pos = lp;
            g_cam.pos.z += g_aimHeight;
        }
    }
    g_cam.valid = true;
}

// ---------------- drawing ----------------
static HFONT Font() {
    if (!g_font)
        g_font = CreateFontW(-14, 0, 0, 0, FW_SEMIBOLD, FALSE, FALSE, FALSE,
                             DEFAULT_CHARSET, OUT_TT_PRECIS, CLIP_DEFAULT_PRECIS,
                             ANTIALIASED_QUALITY, FF_DONTCARE, L"Consolas");
    return g_font;
}

static void Text(HDC dc, int x, int y, const wchar_t* s, COLORREF c) {
    SetTextColor(dc, c);
    TextOutW(dc, x, y, s, (int)wcslen(s));
}

static void Fill(HDC dc, float x, float y, float w, float h, COLORREF c) {
    HBRUSH b = CreateSolidBrush(c);
    RECT r{ (LONG)x, (LONG)y, (LONG)(x + w), (LONG)(y + h) };
    FillRect(dc, &r, b);
    DeleteObject(b);
}

static void Draw() {
    if (!g_dc) return;

    HBRUSH black = CreateSolidBrush(RGB(0, 0, 0));
    RECT full{ 0, 0, g_w, g_h };
    FillRect(g_dc, &full, black);
    DeleteObject(black);

    SelectObject(g_dc, Font());
    SetBkMode(g_dc, TRANSPARENT);

    if (g_espOn) {
        for (size_t i = 0; i < g_players.size(); ++i) {
            const Player& p = g_players[i];
            if (!p.onScreen) continue;
            if (p.head.x < -40.f || p.head.x > g_w + 40.f) continue;
            if (p.head.y < -40.f || p.head.y > g_h + 40.f) continue;

            Fill(g_dc, p.head.x - 4.f, p.head.y - 4.f, 9.f, 9.f, RGB(1, 1, 1));
            Fill(g_dc, p.head.x - 3.f, p.head.y - 3.f, 7.f, 7.f, RGB(0, 255, 120));

            wchar_t nb[16];
            swprintf_s(nb, L"%d", (int)p.dist);
            Text(g_dc, (int)p.head.x + 7, (int)p.head.y - 6, nb, RGB(160, 255, 160));
        }
    }

    if (g_showDebug) {
        std::vector<std::wstring> lines;
        wchar_t buf[256];

        lines.push_back(L"ESP LOADED");

        swprintf_s(buf, L"ents %d | sane %d | dist %d | dots %d",
                   g_entCount, g_saneEnts, g_distOk, (int)g_players.size());
        lines.push_back(buf);

        swprintf_s(buf, L"cam %.1f %.1f %.1f  maxD %.0f  noDist %d",
                   (double)g_cam.pos.x, (double)g_cam.pos.y, (double)g_cam.pos.z,
                   (double)g_maxDist, (int)g_noDist);
        lines.push_back(buf);

        swprintf_s(buf, L"dmin %.1f  dmax %.1f", (double)g_dMin, (double)g_dMax);
        lines.push_back(buf);

        swprintf_s(buf, L"e0 %.1f %.1f %.1f",
                   (double)g_dump[0][0], (double)g_dump[0][1], (double)g_dump[0][2]);
        lines.push_back(buf);

        {
            wchar_t t1[160];
            wchar_t t2[128];
            swprintf_s(t1, L"rescan 0x%llX spread %d box %.1f",
                       (unsigned long long)g_foundPos, (int)g_posSpread, (double)g_posBox);
            swprintf_s(t2, L"camOff 0x%llX cands %d  localEnt %llX",
                       (unsigned long long)g_off.CameraPosition, (int)g_camCands.size(),
                       (unsigned long long)g_localEnt);
            lines.push_back(t1);
            lines.push_back(t2);
        }

        lines.push_back(g_status.empty() ? L"status OK" : g_status);

        swprintf_s(buf, L"G 0x%llX L 0x%llX P 0x%llX C 0x%llX",
                   (unsigned long long)g_off.Game, (unsigned long long)g_off.EntityList,
                   (unsigned long long)g_off.EntityPosition, (unsigned long long)g_off.EntityCount);
        lines.push_back(buf);

        swprintf_s(buf, L"hunt scan %d ptr %d wld %d ctl %d cam %d ent %d",
                   g_hScan, g_hPtr, g_hWorld, g_hCtrl, g_hCam, g_hEnt);
        lines.push_back(buf);

        if (!g_gameHits.empty()) {
            const GameHit& hit = g_gameHits[0];
            swprintf_s(buf, L"HITS %d  g 0x%llX list 0x%llX pos 0x%llX  (F4)",
                       (int)g_gameHits.size(), (unsigned long long)hit.game,
                       (unsigned long long)hit.listOff, (unsigned long long)hit.posOff);
            lines.push_back(buf);
        }

        lines.push_back(L"F1 dots  F2 debug  F3 hunt  F4 apply");
        lines.push_back(L"F7 noDist  F8 find pos  F9 fix cam");

        int y = 8;
        for (size_t i = 0; i < lines.size(); ++i) {
            Text(g_dc, 10, y, lines[i].c_str(), RGB(0, 220, 255));
            y += 17;
        }
    }

    Fill(g_dc, g_w * 0.5f - 6.f, g_h * 0.5f, 12.f, 1.f, RGB(0, 255, 120));
    Fill(g_dc, g_w * 0.5f, g_h * 0.5f - 6.f, 1.f, 12.f, RGB(0, 255, 120));

    g_dMin = 1.0e9f;
    g_dMax = -1.0e9f;
}

// ---------------- window ----------------
static LRESULT CALLBACK WndProc(HWND h, UINT m, WPARAM wp, LPARAM lp) {
    switch (m) {
        case WM_ERASEBKGND:
            return 1;
        case WM_PAINT: {
            PAINTSTRUCT ps;
            HDC dc = BeginPaint(h, &ps);
            g_dc = dc;
            Draw();
            g_dc = nullptr;
            EndPaint(h, &ps);
            return 0;
        }
        case WM_DESTROY:
            PostQuitMessage(0);
            return 0;
    }
    return DefWindowProcW(h, m, wp, lp);
}

static bool KeyPressed(int vk) {
    static bool down[256] = {};
    if (vk < 0 || vk > 255) return false;
    bool now = (GetAsyncKeyState(vk) & 0x8000) != 0;
    bool was = down[vk];
    down[vk] = now;
    return now && !was;
}

static DWORD WINAPI MainThread(LPVOID) {
    g_base = reinterpret_cast<uintptr_t>(GetModuleHandleW(nullptr));
    g_w = GetSystemMetrics(SM_CXSCREEN);
    g_h = GetSystemMetrics(SM_CYSCREEN);
    if (g_w <= 0 || g_h <= 0) { g_w = 1920; g_h = 1080; }

    WNDCLASSEXW wc{};
    wc.cbSize = sizeof(wc);
    wc.lpfnWndProc = WndProc;
    wc.hInstance = g_hSelf;
    wc.hCursor = LoadCursorW(nullptr, (LPCWSTR)IDC_ARROW);
    wc.lpszClassName = L"ReforgerEsp";
    RegisterClassExW(&wc);

    g_hwnd = CreateWindowExW(
        WS_EX_LAYERED | WS_EX_TRANSPARENT | WS_EX_TOOLWINDOW | WS_EX_NOACTIVATE,
        L"ReforgerEsp", L"esp", WS_POPUP, 0, 0, g_w, g_h,
        nullptr, nullptr, g_hSelf, nullptr);
    if (!g_hwnd) return 0;

    SetLayeredWindowAttributes(g_hwnd, RGB(0, 0, 0), 0, LWA_COLORKEY);
    SetWindowDisplayAffinity(g_hwnd, WDA_EXCLUDEFROMCAPTURE);
    ShowWindow(g_hwnd, SW_SHOW);
    SetWindowPos(g_hwnd, HWND_TOPMOST, 0, 0, g_w, g_h, SWP_NOACTIVATE);

    while (g_running) {
        MSG msg;
        while (PeekMessageW(&msg, nullptr, 0, 0, PM_REMOVE)) {
            TranslateMessage(&msg);
            DispatchMessageW(&msg);
        }

        if (KeyPressed(VK_F1)) g_espOn = !g_espOn;
        if (KeyPressed(VK_F2)) g_showDebug = !g_showDebug;
        if (KeyPressed(VK_F3)) HuntGame();
        if (KeyPressed(VK_F4) && !g_gameHits.empty()) {
            static size_t idx = 0;
            const GameHit& hit = g_gameHits[idx % g_gameHits.size()];
            g_off.Game = hit.game;
            if (hit.listOff) g_off.EntityList = hit.listOff;
            if (hit.posOff)  g_off.EntityPosition = hit.posOff;
            if (hit.cntOff)  g_off.EntityCount = hit.cntOff;
            idx++;
        }
        if (KeyPressed(VK_F7)) g_noDist = !g_noDist;
        if (KeyPressed(VK_F8)) RescanEntityPosition();
        if (KeyPressed(VK_F9)) FixCamera();

        Update();
        InvalidateRect(g_hwnd, nullptr, FALSE);

        MSG paint;
        while (PeekMessageW(&paint, nullptr, 0, 0, PM_REMOVE)) {
            TranslateMessage(&paint);
            DispatchMessageW(&paint);
        }

        Sleep(8);
    }

    if (g_hwnd) DestroyWindow(g_hwnd);
    return 0;
}

BOOL APIENTRY DllMain(HMODULE hModule, DWORD reason, LPVOID) {
    if (reason == DLL_PROCESS_ATTACH) {
        DisableThreadLibraryCalls(hModule);
        g_hSelf = hModule;
        g_running = true;
        HANDLE t = CreateThread(nullptr, 0, MainThread, nullptr, 0, nullptr);
        if (t) CloseHandle(t);
    } else if (reason == DLL_PROCESS_DETACH) {
        g_running = false;
    }
    return TRUE;
}
