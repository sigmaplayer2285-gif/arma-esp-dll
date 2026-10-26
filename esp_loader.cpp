// esp_loader.cpp - injected ESP skeleton
#define WIN32_LEAN_AND_MEAN
#define NOMINMAX
#include <windows.h>
#include <cstdint>
#include <atomic>

#pragma comment(lib, "gdi32.lib")
#pragma comment(lib, "user32.lib")

static HMODULE           g_hSelf   = nullptr;
static HWND              g_hwnd    = nullptr;
static std::atomic<bool> g_running{ false };
static uintptr_t         g_base    = 0;

// ---------- in-process read: no handle, so BattlEye can't block it ----------
template <typename T>
static inline T Read(uintptr_t a) {
    if (a < 0x10000 || a > 0x7FFFFFFFFFFFull) return T{};
    return *reinterpret_cast<T*>(a);
}

// ---------- same offsets as your external tool ----------
static uintptr_t OFF_Game      = 0x1D4FCE8;
static uintptr_t OFF_GameWorld = 0x130;

// ---------- overlay ----------
static void Draw(HDC dc, int w, int h) {
    HBRUSH bg = CreateSolidBrush(RGB(0, 0, 0));   // pure black is the key colour
    RECT rc{ 0, 0, w, h };
    FillRect(dc, &rc, bg);
    DeleteObject(bg);

    HPEN pen = CreatePen(PS_SOLID, 1, RGB(0, 255, 130));
    HPEN old = (HPEN)SelectObject(dc, pen);
    SelectObject(dc, GetStockObject(NULL_BRUSH));
    Ellipse(dc, w / 2 - 120, h / 2 - 120, w / 2 + 120, h / 2 + 120);
    MoveToEx(dc, w / 2 - 12, h / 2, nullptr); LineTo(dc, w / 2 + 12, h / 2);
    MoveToEx(dc, w / 2, h / 2 - 12, nullptr); LineTo(dc, w / 2, h / 2 + 12);
    SelectObject(dc, old);
    DeleteObject(pen);
}

static LRESULT CALLBACK WndProc(HWND h, UINT m, WPARAM w, LPARAM l) {
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
    return DefWindowProcW(h, m, w, l);
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

// ---------- injected thread ----------
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
        }

        InvalidateRect(g_hwnd, nullptr, FALSE);
        Sleep(1);
    }

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
