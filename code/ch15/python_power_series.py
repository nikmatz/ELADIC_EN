# ============================================================
# python_power_series.py
# Chapter 14 — Power Series
# Matzakos, N. (2026). Elements of Linear Algebra, Differential & Integral Calculus. NewTech Publications.
# ============================================================
#
# LIBRARIES:
#   sympy              → taylor/series, radius R, operations
#   numpy              → numerical approximations
#   scipy.integrate    → numerical integral (for comparison)
#   matplotlib         → power series plots
#
# BASIC COMMANDS:
#   sympy.series(f, x, x0, n)    → Taylor expansion
#   sympy.Interval               → interval of convergence
#   np.polyval                   → evaluation of a polynomial
# ============================================================

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec
from sympy import (symbols, series, diff, integrate, limit, oo,
                   sin, cos, exp, log, atan, sqrt, Rational,
                   factorial, simplify, lambdify, pi, S,
                   summation, Abs, pprint)
from scipy.integrate import quad
from math import factorial as mfact

x, n = symbols('x n', real=True)

print("=" * 55)
print(" Chapter 14: Power Series — Python")
print("=" * 55)

# ── A. Radius of Convergence ─────────────────────
print("\n── A. Radius of Convergence R ──")

power_series_info = [
    ("Sum x^n/n",    Rational(1,1),  "[-1, 1)",  "ln(1/(1-x))"),
    ("Sum x^n/n!",   oo,             "(-∞,+∞)",  "e^x"),
    ("Sum n·x^n",    Rational(1,1),  "(-1, 1)",  "x/(1-x)²"),
    ("Sum (x/2)^n",  Rational(2,1),  "(-2, 2)",  "2/(2-x)"),
    ("Sum (-1)^n x^n/(2n+1)", Rational(1,1), "[-1, 1]", "arctan(x)"),
    ("Sum n!·x^n",   Rational(0,1),  "{0}",      "diverges"),
]

print(f"{'Series':<24} {'R':>8}  {'Interval':<12}  {'Sum'}")
print("-" * 62)
for label, R, interval, total in power_series_info:
    Rstr = "∞" if R == oo else str(float(R))
    print(f"  {label:<22}  {Rstr:>8}  {interval:<12}  {total}")

# ── B. Taylor Expansions ───────────────────────
print("\n── B. Maclaurin Expansions ──")

taylor_cases = [
    (exp(x),    "e^x"),
    (sin(x),    "sin x"),
    (cos(x),    "cos x"),
    (log(1+x),  "ln(1+x)"),
    (1/(1-x),   "1/(1-x)"),
    (atan(x),   "arctan x"),
    (sqrt(1+x), "sqrt(1+x)"),
]

for f_sym, label in taylor_cases:
    T = series(f_sym, x, 0, 8)
    print(f"  {label}: {T}")

# ── C. Operations with Power Series ────────────────
print("\n── C. Operations: Derivative & Integral ──")

# Derivative: d/dx[1/(1-x)] = Sum n·x^(n-1) = 1/(1-x)²
T_geo = series(1/(1-x), x, 0, 8)
dT    = diff(T_geo, x)
print(f"  d/dx[1/(1-x)] = {dT}")
print(f"  = Sum n·x^(n-1)  (= 1/(1-x)²)")

# Integral: ∫1/(1+x)dx = ln(1+x)
T_1px = series(1/(1+x), x, 0, 8)
IT    = integrate(T_1px, x)
print(f"\n  ∫ 1/(1+x) dx = {IT}")
print(f"  = Sum (-1)^n·x^(n+1)/(n+1) = ln(1+x)")

# ── D. Computing pi ──────────────────────────
print("\n── D. Computing pi with the Gregory-Leibniz Series ──")
print("pi/4 = 1 - 1/3 + 1/5 - 1/7 + ...")
exact_pi = float(pi)
for N in [10, 100, 1_000, 10_000]:
    S = sum((-1)**k / (2*k+1) for k in range(N+1))
    pi_approx = 4*S
    err = abs(pi_approx - exact_pi)
    print(f"  N={N:6d}: pi ≈ {pi_approx:.10f}  error={err:.2e}")

# Machin's formula — much faster convergence
print("\nMachin's formula: pi/4 = 4·arctan(1/5) - arctan(1/239)")
def arctan_series(x_val, terms=15):
    return sum((-1)**k * x_val**(2*k+1) / (2*k+1) for k in range(terms))

pi_machin = 4 * (4*arctan_series(1/5) - arctan_series(1/239))
print(f"  pi ≈ {pi_machin:.15f}")
print(f"  pi  = {exact_pi:.15f}  error={abs(pi_machin-exact_pi):.2e}")

# ── E. Approximating an Integral ──────────────────
print("\n── E. Power Series for Evaluating an Integral ──")

# ∫₀¹ sin(x²) dx — Fresnel integral
T_sinx2 = series(sin(x**2), x, 0, 15)
I_sym   = integrate(T_sinx2, (x, 0, 1))
I_num, _= quad(lambda t: np.sin(t**2), 0, 1)
print(f"  ∫₀¹ sin(x²) dx:")
print(f"    Power series ≈ {float(I_sym):.10f}")
print(f"    scipy.quad   ≈ {I_num:.10f}")
print(f"    Difference:    {abs(float(I_sym)-I_num):.2e}")

# ∫₀^(1/2) arctan(x)/x dx
T_ax = series(atan(x)/x, x, 0, 10)
I_ax = integrate(T_ax, (x, 0, Rational(1,2)))
I_ax_num, _ = quad(lambda t: np.arctan(t)/t if t > 0 else 1, 0, 0.5)
print(f"\n  ∫₀^(1/2) arctan(x)/x dx:")
print(f"    Power series ≈ {float(I_ax):.10f}")
print(f"    scipy.quad   ≈ {I_ax_num:.10f}")

# ── F. Plots ──────────────────────────────
print("\n── F. Plots ──")

fig = plt.figure(figsize=(14, 9))
fig.suptitle("Power Series — Taylor/Maclaurin", fontsize=13, fontweight='bold')
gs = gridspec.GridSpec(2, 3, fig, hspace=0.45, wspace=0.35)

# 1. e^x — Maclaurin approximations
ax1 = fig.add_subplot(gs[0, 0])
xv = np.linspace(-3, 3, 500)
ax1.plot(xv, np.exp(xv), 'k', lw=2.5, label=r'$e^x$', zorder=5)
colors = ['royalblue', 'tomato', 'forestgreen', 'orange', 'purple']
for order, col in zip([1, 2, 3, 5, 8], colors):
    Tapprox = sum(xv**k / mfact(k) for k in range(order+1))
    ax1.plot(xv, np.clip(Tapprox, -5, 25), ls='--', lw=1.5,
             color=col, label=f'n={order}')
ax1.set_ylim(-1, 15); ax1.set_xlim(-3, 3)
ax1.set_title(r"Maclaurin $e^x$", fontsize=10)
ax1.legend(fontsize=7, ncol=2); ax1.grid(True, alpha=0.3)

# 2. sin x — Maclaurin
ax2 = fig.add_subplot(gs[0, 1])
xv2 = np.linspace(-2*np.pi, 2*np.pi, 500)
ax2.plot(xv2, np.sin(xv2), 'k', lw=2.5, label=r'$\sin x$', zorder=5)
for order, col in zip([1, 3, 5, 9], colors):
    T2 = sum((-1)**k * xv2**(2*k+1)/mfact(2*k+1)
             for k in range(order//2 + 1))
    ax2.plot(xv2, np.clip(T2, -4, 4), ls='--', lw=1.5,
             color=col, label=f'n={2*(order//2+1)-1}')
ax2.set_ylim(-3, 3); ax2.set_xlim(-2*np.pi, 2*np.pi)
ax2.set_title(r"Maclaurin $\sin x$", fontsize=10)
ax2.legend(fontsize=7, ncol=2); ax2.grid(True, alpha=0.3)

# 3. arctan x — series → pi
ax3 = fig.add_subplot(gs[0, 2])
xv3 = np.linspace(-1.2, 1.2, 400)
ax3.plot(xv3, np.arctan(xv3), 'k', lw=2.5, label=r'$\arctan x$', zorder=5)
for order, col in zip([1, 3, 7, 13], colors):
    T3 = sum((-1)**k * xv3**(2*k+1)/(2*k+1)
             for k in range(order//2 + 1))
    ax3.plot(xv3, T3, ls='--', lw=1.5, color=col, label=f'n={order}')
ax3.axhline(np.pi/4, color='gray', ls=':', lw=1)
ax3.axvline(1, color='gray', ls=':', lw=1)
ax3.set_title(r"Maclaurin $\arctan x$", fontsize=10)
ax3.legend(fontsize=7, ncol=2); ax3.grid(True, alpha=0.3)

# 4. ln(1+x)
ax4 = fig.add_subplot(gs[1, 0])
xv4 = np.linspace(-0.9, 2, 400)
ax4.plot(xv4, np.log(1+xv4), 'k', lw=2.5, label=r'$\ln(1+x)$', zorder=5)
for order, col in zip([1, 2, 4, 7], colors):
    T4 = sum((-1)**(k+1) * xv4**k / k for k in range(1, order+1))
    ax4.plot(xv4, np.clip(T4, -3, 3), ls='--', lw=1.5,
             color=col, label=f'n={order}')
ax4.set_ylim(-2, 2); ax4.set_xlim(-0.9, 2)
ax4.set_title(r"Maclaurin $\ln(1+x)$", fontsize=10)
ax4.legend(fontsize=7, ncol=2); ax4.grid(True, alpha=0.3)

# 5. Convergence of Gregory-Leibniz to pi
ax5 = fig.add_subplot(gs[1, 1])
Ns5 = np.arange(1, 201)
pi_approx5 = [4*sum((-1)**k/(2*k+1) for k in range(N)) for N in Ns5]
ax5.plot(Ns5, pi_approx5, 'royalblue', lw=1.5, label=r'$4\sum(-1)^n/(2n+1)$')
ax5.axhline(np.pi, color='tomato', ls='--', lw=2, label=f'pi={np.pi:.6f}')
ax5.set_xlabel('N'); ax5.set_title("Gregory-Leibniz → pi", fontsize=10)
ax5.legend(fontsize=8); ax5.grid(True, alpha=0.3)
ax5.set_ylim(2.9, 3.4)

# 6. Taylor error for e^x at various n (log scale)
ax6 = fig.add_subplot(gs[1, 2])
x0 = 2.0  # evaluation at x=2
true_val = np.exp(x0)
orders6  = np.arange(1, 20)
errs6    = [abs(sum(x0**k/mfact(k) for k in range(n+1)) - true_val)
            for n in orders6]
ax6.semilogy(orders6, errs6, 'o-', color='royalblue', lw=2, ms=5)
ax6.set_xlabel('Order n')
ax6.set_ylabel('|error|')
ax6.set_title(r"Maclaurin error for $e^x$ at $x=2$", fontsize=10)
ax6.grid(True, alpha=0.3, which='both')

plt.savefig("power_series.png", dpi=120, bbox_inches='tight')
print("Plot saved: power_series.png")
plt.show()
