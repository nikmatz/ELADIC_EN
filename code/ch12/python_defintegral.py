# ============================================================
# python_defintegral.py
# Chapter 11 — Definite Integral
# Matzakos, N. (2026). Elements of Linear Algebra, Differential & Integral Calculus. NewTech Publications.
# ============================================================
#
# LIBRARIES:
#   sympy              → definite integral (exact)
#   scipy.integrate    → quad (numerical), dblquad
#   numpy              → trapezoidal rule, Simpson
#   matplotlib         → areas, geometric illustrations
#
# BASIC COMMANDS:
#   sympy.integrate(f, (x, a, b))    → exact definite integral
#   scipy.integrate.quad(f, a, b)    → numerical
#   np.trapz(y, x)                   → trapezoidal rule
#   scipy.integrate.simpson(y, x)    → Simpson's rule
# ============================================================

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec
from matplotlib.patches import Polygon
from matplotlib.collections import PatchCollection
from sympy import (symbols, integrate, sin, cos, exp, log,
                   sqrt, Abs, pi, E, Rational, simplify,
                   lambdify, solve, oo, pprint)
from scipy.integrate import quad, simpson as sp_simpson
from scipy.integrate import dblquad

x = symbols('x')

print("=" * 55)
print(" Chapter 11: Definite Integral — Python")
print("=" * 55)

# ── A. Basic Definite Integrals ───────────────────
print("\n── A. Basic Definite Integrals ──")

def_integrals = [
    (x**2,            0, 3,      "∫₀³ x² dx",         Rational(9,1)),
    (sin(x),          0, pi,     "∫₀^pi sin x dx",     2),
    (exp(x),          0, 1,      "∫₀¹ eˣ dx",          E - 1),
    (1/x,             1, E,      "∫₁^e (1/x) dx",      1),
    (x**3-2*x+1,     -1, 2,      "∫₋₁² (x³-2x+1) dx", Rational(15,4)),
    (cos(x),          0, pi/2,   "∫₀^(pi/2) cos x dx", 1),
    (1/(x**2+1),      0, 1,      "∫₀¹ 1/(x²+1) dx",    pi/4),
]

print(f"{'Integral':<28} {'Exact':>12}  {'float':>12}  {'✓'}")
print("-" * 60)
for f_sym, a, b, label, expected in def_integrals:
    val = integrate(f_sym, (x, a, b))
    val_f = float(val)
    exp_f = float(expected)
    ok = abs(val_f - exp_f) < 1e-9
    print(f"  {label:<26}  {str(val):>12}  {val_f:>12.8f}  {'✓' if ok else '✗'}")

# ── B. Properties ──────────────────────────────
print("\n── B. Properties of the Definite Integral ──")

f_prop = x**2 - x
I_0_2 = float(integrate(f_prop, (x, 0, 2)))
I_0_1 = float(integrate(f_prop, (x, 0, 1)))
I_1_2 = float(integrate(f_prop, (x, 1, 2)))
print(f"  Additivity: ∫₀²f = ∫₀¹f + ∫₁²f  →  "
      f"{I_0_2:.6f} = {I_0_1:.6f} + {I_1_2:.6f}  "
      f"{'✓' if abs(I_0_2-(I_0_1+I_1_2))<1e-10 else '✗'}")

I_fwd = float(integrate(x**3, (x, 1, 3)))
I_bwd = float(integrate(x**3, (x, 3, 1)))
print(f"  Reversal: ∫₁³ x³ = {I_fwd:.4f},  ∫₃¹ x³ = {I_bwd:.4f}  "
      f"(sum={I_fwd+I_bwd:.4f} ✓)")

# ── C. Area between Curves ──────────────────────
print("\n── C. Area between Curves ──")

areas = [
    (x,       x**2,   0,  1,    "y=x  vs  y=x²      [0,1]"),
    (sin(x),  cos(x), 0,  pi/4, "sinx vs cosx       [0,pi/4]"),
    (-x**2+4, x**2-2*x, -1, 2, "y=-x²+4 vs y=x²-2x [-1,2]"),
]

for f_up, f_dn, a, b, label in areas:
    A = integrate(f_up - f_dn, (x, a, b))
    print(f"  {label}")
    print(f"    Area = {A} = {float(A):.6f}")

# ── D. Numerical Integration ─────────────────────
print("\n── D. Numerical Integration (scipy.quad) ──")

numerical_cases = [
    (lambda t: np.exp(t**2),      0, 1,       "∫₀¹ eˣ² dx        (transcendental)"),
    (lambda t: np.sin(t**2),      0, 1,       "∫₀¹ sin(x²) dx    (Fresnel)"),
    (lambda t: np.sin(t)/t if t != 0 else 1.0, 1e-10, np.pi, "∫₀^pi sinc(x) dx"),
    (lambda t: 1/np.sqrt(1-t**2+1e-12), 0, 0.99, "∫₀¹ 1/√(1-x²) dx  (→ pi/2)"),
]

for f_np, a, b, label in numerical_cases:
    val, err = quad(f_np, a, b)
    print(f"  {label}")
    print(f"    ≈ {val:.10f}  (error ≤ {err:.2e})")

# ── E. Trapezoidal Rule & Simpson ───────────────────
print("\n── E. Trapezoidal Rule & Simpson ──")

def trapezoid_rule(f, a, b, n):
    xi = np.linspace(a, b, n+1)
    yi = f(xi)
    return np.trapz(yi, xi)

def simpsons_rule(f, a, b, n):
    if n % 2 != 0:
        n += 1
    xi = np.linspace(a, b, n+1)
    yi = f(xi)
    return sp_simpson(yi, x=xi)

# Comparison for ∫₀¹ x² dx (exact = 1/3)
f_test = lambda t: t**2
exact  = 1/3
print(f"  ∫₀¹ x² dx  (exact = {exact:.10f})")
for n in [4, 8, 16, 32]:
    T = trapezoid_rule(f_test, 0, 1, n)
    S = simpsons_rule(f_test, 0, 1, n)
    print(f"    n={n:2d}:  Trapezoid={T:.10f} (err={abs(T-exact):.2e})"
          f"   Simpson={S:.10f} (err={abs(S-exact):.2e})")

# Comparison for ∫₀^pi sinx dx (exact = 2)
f_sin = np.sin
exact2 = 2.0
print(f"\n  ∫₀^pi sinx dx  (exact = 2)")
for n in [4, 8, 16]:
    T = trapezoid_rule(f_sin, 0, np.pi, n)
    S = simpsons_rule(f_sin, 0, np.pi, n)
    print(f"    n={n:2d}:  Trapezoid={T:.8f} (err={abs(T-exact2):.2e})"
          f"   Simpson={S:.8f} (err={abs(S-exact2):.2e})")

# ── F. Plots ─────────────────────────────────
print("\n── F. Plots ──")

fig = plt.figure(figsize=(14, 9))
fig.suptitle("Definite Integral", fontsize=13, fontweight='bold')
gs = gridspec.GridSpec(2, 3, fig, hspace=0.45, wspace=0.35)

# 1. ∫₀³ x² dx — shaded region
ax1 = fig.add_subplot(gs[0, 0])
t1 = np.linspace(-0.3, 3.5, 400)
y1 = t1**2
ax1.plot(t1, y1, 'royalblue', lw=2.5, label=r'$f(x)=x^2$')
tx = np.linspace(0, 3, 200)
ax1.fill_between(tx, tx**2, alpha=0.25, color='royalblue',
                  label=r'$\int_0^3 x^2\,dx=9$')
ax1.axhline(0, color='k', lw=0.5)
ax1.set_xlim(-0.3, 3.5); ax1.set_ylim(-0.5, 10)
ax1.set_title(r"$\int_0^3 x^2\,dx = 9$", fontsize=10)
ax1.legend(fontsize=8); ax1.grid(True, alpha=0.3)

# 2. Area between y=x and y=x²
ax2 = fig.add_subplot(gs[0, 1])
t2 = np.linspace(-0.2, 1.3, 400)
ax2.plot(t2, t2,    'royalblue', lw=2.5, label=r'$y=x$')
ax2.plot(t2, t2**2, 'tomato',    lw=2.5, label=r'$y=x^2$')
tx2 = np.linspace(0, 1, 200)
ax2.fill_between(tx2, tx2**2, tx2, alpha=0.25, color='green',
                  label=r'$A=\frac{1}{6}$')
ax2.axhline(0, color='k', lw=0.5)
ax2.set_title(r"Area: $y=x$ vs $y=x^2$", fontsize=10)
ax2.legend(fontsize=8); ax2.grid(True, alpha=0.3)

# 3. ∫₀^pi sinx dx = 2
ax3 = fig.add_subplot(gs[0, 2])
t3 = np.linspace(-0.2, np.pi+0.2, 400)
ax3.plot(t3, np.sin(t3), 'royalblue', lw=2.5, label=r'$\sin x$')
tx3 = np.linspace(0, np.pi, 200)
ax3.fill_between(tx3, np.sin(tx3), alpha=0.25, color='royalblue',
                  label=r'$\int_0^\pi \sin x\,dx=2$')
ax3.axhline(0, color='k', lw=0.8)
ax3.set_xticks([0, np.pi/2, np.pi])
ax3.set_xticklabels(['0', r'$\pi/2$', r'$\pi$'])
ax3.set_title(r"$\int_0^\pi \sin x\,dx = 2$", fontsize=10)
ax3.legend(fontsize=8); ax3.grid(True, alpha=0.3)

# 4. Area between two parabolas
ax4 = fig.add_subplot(gs[1, 0])
t4 = np.linspace(-1.5, 2.5, 400)
y4a = -t4**2 + 4
y4b = t4**2 - 2*t4
ax4.plot(t4, y4a, 'royalblue', lw=2.5, label=r'$y=-x^2+4$')
ax4.plot(t4, y4b, 'tomato',    lw=2.5, label=r'$y=x^2-2x$')
tx4 = np.linspace(-1, 2, 200)
ax4.fill_between(tx4, tx4**2-2*tx4, -tx4**2+4, alpha=0.25, color='green',
                  label='Area=9')
ax4.axhline(0, color='k', lw=0.5)
ax4.set_ylim(-3, 6)
ax4.set_title("Area between two parabolas", fontsize=10)
ax4.legend(fontsize=8); ax4.grid(True, alpha=0.3)

# 5. Trapezoid vs Simpson comparison (error)
ax5 = fig.add_subplot(gs[1, 1])
ns   = [2, 4, 8, 16, 32, 64]
trap_errs = [abs(trapezoid_rule(lambda t: t**2, 0, 1, n) - 1/3) for n in ns]
simp_errs = [abs(simpsons_rule( lambda t: t**2, 0, 1, n) - 1/3) for n in ns]
ax5.loglog(ns, trap_errs, 'o-', color='royalblue', lw=2, label='Trapezoid')
ax5.loglog(ns, simp_errs, 's-', color='tomato',    lw=2, label='Simpson')
ax5.set_xlabel('n'); ax5.set_ylabel('|error|')
ax5.set_title(r"Convergence: $\int_0^1 x^2\,dx$", fontsize=10)
ax5.legend(fontsize=8); ax5.grid(True, alpha=0.3, which='both')

# 6. Numerical vs Exact (bar chart of errors)
ax6 = fig.add_subplot(gs[1, 2])
labels6 = [r'$\int_0^1 x^2$', r'$\int_0^\pi \sin x$', r'$\int_0^1 e^x$', r'$\int_1^e 1/x$']
exact6  = [1/3, 2, np.e-1, 1]
num6    = [quad(lambda t: t**2, 0, 1)[0],
           quad(np.sin, 0, np.pi)[0],
           quad(np.exp, 0, 1)[0],
           quad(lambda t: 1/t, 1, np.e)[0]]
errs6   = [abs(n-e) for n,e in zip(num6, exact6)]
bars = ax6.bar(labels6, errs6, color=['royalblue','tomato','forestgreen','orange'])
ax6.set_ylabel('|error|'); ax6.set_yscale('log')
ax6.set_title("scipy.quad: Error", fontsize=10)
ax6.grid(True, alpha=0.3, axis='y')
for bar, err in zip(bars, errs6):
    ax6.text(bar.get_x()+bar.get_width()/2, bar.get_height()*1.5,
             f'{err:.0e}', ha='center', va='bottom', fontsize=7)

plt.savefig("definite_integrals.png", dpi=120, bbox_inches='tight')
print("Plot saved: definite_integrals.png")
plt.show()
