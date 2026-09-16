# ============================================================
# python_ttl.py
# Chapter 15 — Fundamental Theorem of Calculus (FTC)
# Matzakos, N. (2026). Elements of Linear Algebra, Differential & Integral Calculus. NewTech Publications.
# ============================================================
#
# LIBRARIES:
#   sympy       → symbolic area function and Leibniz rule
#   numpy       → cumulative sum of strips (np.cumsum)
#   scipy       → reference numerical integration (quad)
#   matplotlib  → combined plots and fill_between
#
# BASIC COMMANDS:
#   sympy.integrate(f, (t, 0, x)) → F(x) = ∫₀ˣ f(t)dt
#   sympy.diff(F, x)              → F'(x) = f(x)          [FTC Part I]
#   sympy.Integral(f, (t, a(x), b(x))) → unevaluated integral
#   sympy.diff(Integral, x)       → Leibniz rule
#   scipy.integrate.quad(f, a, b) → numerical integral
#   numpy.cumsum(y) * h           → cumulative sum of strips
#   matplotlib.fill_between()     → shading of a region
#
# Book activity:
#   (a) F(x)=∫₀ˣf(t)dt for three f's; check F'=f; f and F on ONE plot
#   (b) np.cumsum for f(x)=sin x on [0,2pi] versus the exact 1-cos x
#   (c) Leibniz rule for d/dx ∫ₓ^(x²) sin(t²)dt + finite differences
#   (d) MVT for Integrals for f(x)=x² on [0,3]
# ============================================================

import numpy as np
import sympy as sp
import matplotlib.pyplot as plt
from scipy.integrate import quad

x, t = sp.symbols('x t', real=True)

print("=" * 62)
print(" Chapter 15: Fundamental Theorem of Calculus")
print("=" * 62)

# ── A. (a) The area function F(x) = ∫₀ˣ f(t)dt ─────────
print("\n──── A. (a) Area function and the check F'(x) = f(x) ────")

cases = [("t²",        t**2,          (-2.0,  2.0)),
         ("sin t",     sp.sin(t),     (0.0,   2*np.pi)),
         ("1/(1+t²)",  1/(1 + t**2),  (-4.0,  4.0))]

fig, axes = plt.subplots(1, 3, figsize=(14, 4.3))
fig.suptitle("FTC Part I:  F(x) = ∫₀ˣ f(t)dt  and  F'(x) = f(x)",
             fontsize=12, fontweight='bold')

for ax, (name, ft, (lo, hi)) in zip(axes, cases):
    F = sp.simplify(sp.integrate(ft, (t, 0, x)))
    dF = sp.simplify(sp.diff(F, x))
    ok = sp.simplify(dF - ft.subs(t, x)) == 0
    print(f"  f(t) = {name:<10s} → F(x) = {F}")
    print(f"      F'(x) = {dF}     F'(x) - f(x) = 0 ? {ok}")

    # f and F on the SAME plot
    zz = np.linspace(lo, hi, 500)
    fn = sp.lambdify(x, ft.subs(t, x), 'numpy')
    Fn = sp.lambdify(x, F, 'numpy')
    ax.plot(zz, fn(zz) * np.ones_like(zz), 'b-', lw=2, label=f"f(x) = {name}")
    ax.plot(zz, Fn(zz) * np.ones_like(zz), 'r-', lw=2, label=f"F(x) = {F}")
    ax.axhline(0, color='k', lw=.6); ax.axvline(0, color='k', lw=.6)
    ax.set_xlabel("x"); ax.legend(fontsize=8); ax.grid(alpha=.3)

plt.tight_layout()
print("\n  [Expected: x**3/3 ,  1 - cos(x) ,  atan(x)]")

# ── B. (b) Numerical area function with np.cumsum ──────
print("\n──── B. (b) np.cumsum for f(x) = sin x on [0, 2pi] ────")

N = 4001
xs = np.linspace(0, 2*np.pi, N)          # the WHOLE of [0,2pi]
h = xs[1] - xs[0]
y = np.sin(xs)

# Cumulative sum of strips (left endpoints) — the simplest way
F_left = np.concatenate(([0.0], np.cumsum(y[:-1]) * h))
# Cumulative sum of trapezoids — more accurate, same idea (np.cumsum)
F_trap = np.concatenate(([0.0], np.cumsum((y[:-1] + y[1:])/2) * h))
F_exact = 1 - np.cos(xs)                 # the exact area function

print(f"  Grid: {N} points on [0, 2pi],  h = {h:.6f}")
print(f"  max|F_cumsum(left) - (1-cos x)| = "
      f"{np.max(np.abs(F_left - F_exact)):.3e}")
print(f"  max|F_cumsum(trapezoid) - (1-cos x)| = "
      f"{np.max(np.abs(F_trap - F_exact)):.3e}")

for x0 in (np.pi/2, np.pi, 3*np.pi/2, 2*np.pi):
    val = quad(np.sin, 0, x0)[0]
    print(f"    quad ∫₀^{x0:.4f} sin t dt = {val: .10f}   "
          f"exact 1-cos = {1-np.cos(x0): .10f}")

# Where does F' vanish and what happens to f there?
dF = np.gradient(F_trap, xs)
k_max = int(np.argmax(F_trap))
print(f"\n  Maximum of F: F({xs[k_max]:.6f}) = {F_trap[k_max]:.6f}"
      f"   [x = pi ≈ {np.pi:.6f}, F(pi) = 2]")
print(f"  There: F'(x) ≈ {dF[k_max]:.3e}  and  f(x) = sin(x) = "
      f"{np.sin(xs[k_max]):.3e}")
interior = slice(3, -3)
print(f"  max|F'(x) - sin x| in the interior = "
      f"{np.max(np.abs(dF[interior] - y[interior])):.3e}")
# The points where the numerical F' changes sign:
# a genuine sign change (product < 0) — ignores the noise around 0
sign_changes = xs[:-1][dF[:-1]*dF[1:] < 0]
print(f"  Sign changes of F' (= zeros of f) on [0,2pi]: "
      f"{np.round(sign_changes, 5)}   [expected x ≈ pi = {np.pi:.5f}]")
print("  ⇒ Where F' = 0, f vanishes; at x = pi, f changes from + to -,")
print("    so F stops increasing and attains its maximum there.")

fig, (axf, axF) = plt.subplots(2, 1, figsize=(8.5, 6.6), sharex=True)
fig.suptitle("Part I numerically: the accumulation of the strips (np.cumsum)",
             fontsize=12, fontweight='bold')
axf.plot(xs, y, 'b-', lw=2, label="f(x) = sin x")
axf.fill_between(xs, 0, y, where=(y >= 0), color='green', alpha=.20,
                 label="positive contribution")
axf.fill_between(xs, 0, y, where=(y < 0), color='red', alpha=.20,
                 label="negative contribution")
axf.axhline(0, color='k', lw=.6); axf.axvline(np.pi, color='gray', ls=':')
axf.legend(fontsize=8); axf.grid(alpha=.3); axf.set_ylabel("f(x)")

axF.plot(xs, F_trap, 'r-', lw=2.4, label="F(x) via np.cumsum")
axF.plot(xs, F_exact, 'k--', lw=1.4, label="exact F(x) = 1 - cos x")
axF.axvline(np.pi, color='gray', ls=':')
axF.plot([np.pi], [2], 'ko', ms=7)
axF.annotate("maximum F(pi) = 2\n(there f = 0)", (np.pi, 2),
             textcoords="offset points", xytext=(12, -28), fontsize=9)
axF.axhline(0, color='k', lw=.6)
axF.set_xlabel("x"); axF.set_ylabel("F(x)")
axF.legend(fontsize=8); axF.grid(alpha=.3)
axF.set_xticks([0, np.pi/2, np.pi, 3*np.pi/2, 2*np.pi])
axF.set_xticklabels(["0", r"$\pi/2$", r"$\pi$", r"$3\pi/2$", r"$2\pi$"])
plt.tight_layout()

# ── C. (c) Leibniz rule with sympy.Integral ───────────
print("\n──── C. (c) Leibniz rule: d/dx ∫ₓ^(x²) sin(t²) dt ────")

I_unev = sp.Integral(sp.sin(t**2), (t, x, x**2))
print(f"  Unevaluated: {I_unev}")
D = sp.simplify(sp.diff(I_unev, x))
print(f"  sympy.diff → {D}")

# The formula f(b(x))·b'(x) - f(a(x))·a'(x)
bx, ax_ = x**2, x
rule = (sp.sin(t**2).subs(t, bx)*sp.diff(bx, x)
        - sp.sin(t**2).subs(t, ax_)*sp.diff(ax_, x))
print(f"  Formula f(b)b' - f(a)a' → {sp.simplify(rule)}")
print(f"  Difference (must be 0): {sp.simplify(D - rule)}")
print("  [EXPECTED 2x·sin(x⁴) - sin(x²)]")

# Numerical verification with central finite differences
print("\n  Verification with finite differences:")
D_num = sp.lambdify(x, D, 'numpy')
g = lambda s: np.sin(s**2)
print(f"  {'x0':>6} {'finite diff.':>18} {'symbolic formula':>18} "
      f"{'|difference|':>12}")
for x0 in (0.7, 1.0, 1.3, 1.8):
    hh = 1e-5
    Ip = quad(g, x0 + hh, (x0 + hh)**2)[0]
    Im = quad(g, x0 - hh, (x0 - hh)**2)[0]
    num = (Ip - Im)/(2*hh)
    sym = float(D_num(x0))
    print(f"  {x0:>6.2f} {num:>18.9f} {sym:>18.9f} {abs(num-sym):>12.2e}")

# ── D. (d) MVT for Integrals ─────────────────────
print("\n──── D. (d) MVT for Integrals: f(x)=x² on [0,3] ────")

c = sp.symbols('c', positive=True)
a_i, b_i = 0, 3
I_val = sp.integrate(x**2, (x, a_i, b_i))
print(f"  ∫₀³ x² dx = {I_val}   [EXPECTED 9]")

sols = sp.solve(sp.Eq(c**2*(b_i - a_i), I_val), c)
print(f"  solve: f(c)·(b-a) = ∫ₐᵇf  ⇒  c = {sols}")
c_val = sols[0]
print(f"  Admissible solution in [0,3]: c = {c_val} ≈ {float(c_val):.10f}"
      f"   [EXPECTED √3 ≈ {np.sqrt(3):.10f}]")
h_rect = c_val**2
print(f"  Height of the rectangle f(c) = {h_rect}")
print(f"  Area of the rectangle f(c)·(b-a) = {sp.simplify(h_rect*(b_i-a_i))}"
      f"   versus  ∫ₐᵇf = {I_val}")
print(f"  Difference (must be 0): {sp.simplify(h_rect*(b_i - a_i) - I_val)}")

cf, hf = float(c_val), float(h_rect)
zz = np.linspace(0, 3, 500)
plt.figure(figsize=(7.8, 5.2))
plt.fill_between(zz, 0, zz**2, color='steelblue', alpha=.35,
                 label="region under f(x)=x²   (area = 9)")
plt.fill_between([0, 3], 0, [hf, hf], color='crimson', alpha=.18,
                 label=f"rectangle of height f(c) = {hf:.0f}   (area = {hf*3:.0f})")
plt.plot(zz, zz**2, 'b-', lw=2.3)
plt.axhline(hf, color='crimson', lw=2, ls='--')
plt.vlines(cf, 0, hf, color='k', ls=':', lw=1.3)
plt.plot([cf], [hf], 'ko', ms=8, zorder=5)
plt.annotate(f"c = √3 ≈ {cf:.4f}", (cf, hf), textcoords="offset points",
             xytext=(12, -22), fontsize=10)
plt.xlim(0, 3); plt.ylim(0, 9.6)
plt.xlabel("x"); plt.ylabel("y")
plt.title("MVT for Integrals: the two areas are equal")
plt.legend(fontsize=9, loc='upper left'); plt.grid(alpha=.3)
plt.tight_layout()

print("\n✓ Chapter 15 completed.")
plt.show()
