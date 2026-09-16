# python_dynamoseires.py — Power Series, Convergence, Plots (Ch. 20)
# Matzakos, N. (2026). Elements of Linear Algebra, Differential & Integral Calculus. NewTech Publications.
# Commands: sympy.series(), sympy.diff(), sympy.integrate(), math.factorial(),
#          scipy.integrate.quad(), matplotlib.pyplot

import math
import numpy as np
import sympy as sp
import matplotlib.pyplot as plt
from scipy.integrate import quad

x = sp.symbols('x', real=True)
n = sp.symbols('n', positive=True, integer=True)

print("=" * 66)
print("POWER SERIES: RADIUS OF CONVERGENCE, MACLAURIN, pi, INTEGRALS")
print("=" * 66)

# ── A. Table of radii of convergence + Maclaurin expansions ─────────────────
print()
print("A1. TABLE OF RADII OF CONVERGENCE   R = lim |c_n / c_(n+1)|")
print("-" * 66)
# We compute lim |c_n/c_(n+1)| directly: this way R = ∞ comes out
# naturally, without any division by 0.
coeffs = [
    (1 / n,               "Sum xⁿ/n",   "1"),
    (1 / sp.factorial(n), "Sum xⁿ/n!",  "oo"),
    (n,                   "Sum n·xⁿ",   "1"),
    (1 / 2**n,            "Sum xⁿ/2ⁿ",  "2"),
    (sp.factorial(n),     "Sum n!·xⁿ",  "0"),
]
print(f"   {'series':12s} {'R':>6s}   expected")
for c, label, expected in coeffs:
    R = sp.limit(sp.Abs(c / c.subs(n, n + 1)), n, sp.oo)
    print(f"   {label:12s} {str(R):>6s}   ({expected})")
print("   R = oo: converges for every x.   R = 0: only at x = 0.")

print()
print("A2. MACLAURIN EXPANSIONS  sympy.series(f, x, 0, 8)")
print("-" * 66)
for f in [sp.exp(x), sp.sin(x), sp.cos(x), sp.log(1 + x),
          1 / (1 - x), sp.atan(x), sp.sqrt(1 + x)]:
    print(f"   {str(f):10s} = {sp.series(f, x, 0, 8)}")
print(f"   Taylor of e^x about x0=1: {sp.series(sp.exp(x), x, 1, 5)}")

# ── B. Maclaurin plots for orders 1, 3, 5, 9 ────────────────────────────────
print()
print("B. MACLAURIN POLYNOMIALS — WHERE EACH ONE DIVERGES")
print("-" * 66)
cases = [
    (sp.exp(x),      'e^x',        (-3.0,  3.0),  (-2, 12),   'R = oo'),
    (sp.sin(x),      'sin x',      (-7.0,  7.0),  (-2.5, 2.5), 'R = oo'),
    (sp.log(1 + x),  'ln(1+x)',    (-0.95, 2.0),  (-4, 2),    'R = 1'),
    (sp.atan(x),     'arctan x',   (-2.0,  2.0),  (-3, 3),    'R = 1'),
]
orders = (1, 3, 5, 9)
fig, axes = plt.subplots(2, 2, figsize=(11, 7.5))
for ax, (f, name, (xa, xb), ylim, Rtxt) in zip(axes.ravel(), cases):
    xv = np.linspace(xa, xb, 600)
    fnum = sp.lambdify(x, f, 'numpy')
    ax.plot(xv, fnum(xv), 'k-', lw=2.2, label=name)
    for o in orders:
        P = sp.series(f, x, 0, o + 1).removeO()
        Pnum = sp.lambdify(x, P + 0 * x, 'numpy')
        ax.plot(xv, Pnum(xv), '--', lw=1.2, label=f'order {o}')
    if Rtxt == 'R = 1':
        ax.axvline(-1, color='gray', ls=':', lw=1)
        ax.axvline(1, color='gray', ls=':', lw=1)
    ax.set_ylim(*ylim)
    ax.set_title(f'{name}   ({Rtxt})')
    ax.legend(fontsize=7, loc='best')
    ax.grid(True, alpha=0.3)
plt.tight_layout()

# Numerical evidence: how far off the order-9 polynomial is at various x
for f, name, _, _, Rtxt in cases:
    P9 = sp.lambdify(x, sp.series(f, x, 0, 10).removeO() + 0 * x, 'numpy')
    fn = sp.lambdify(x, f, 'numpy')
    pts = [0.5, 0.9, 1.1, 2.0] if Rtxt == 'R = 1' else [0.5, 1.0, 3.0, 6.0]
    errs = ", ".join(f"x={p}: {abs(float(P9(p)) - float(fn(p))):.2e}" for p in pts)
    print(f"   |P9 - {name:9s}|  {errs}   ({Rtxt})")
print("   For R = 1 the error explodes as soon as we pass |x| = 1;")
print("   for R = oo it decays everywhere, just more slowly as we move away.")

# ── C. Computing pi ─────────────────────────────────────────────────────────
print()
print("C. COMPUTING pi: Gregory–Leibniz (slow) vs Machin (fast)")
print("-" * 66)

def atan_series(z, K):
    """Sum_{k=0}^{K-1} (-1)^k z^(2k+1)/(2k+1) — the arctan series."""
    return sum((-1)**k * z**(2 * k + 1) / (2 * k + 1) for k in range(K))

def gregory_leibniz(N):
    """pi/4 = Sum_{k=0}^{N} (-1)^k/(2k+1) — the arctan series for z = 1."""
    return 4.0 * atan_series(1.0, N + 1)

def machin(K):
    return 4.0 * (4 * atan_series(1 / 5, K) - atan_series(1 / 239, K))

for N in (10, 100, 1000):
    v = gregory_leibniz(N)
    print(f"   Gregory–Leibniz, N = {N:5d}: {v:.12f}   error {abs(v - np.pi):.3e}")
for K in (2, 5, 10):
    v = machin(K)
    print(f"   Machin,          {K:5d} terms: {v:.12f}   error {abs(v - np.pi):.3e}")
print(f"   pi = {np.pi:.12f}")
print("   Gregory–Leibniz gains ~1 digit per tenfold increase in the terms (1/N);")
print("   Machin gains ~1.4 digits PER TERM (geometric convergence, ratio 1/25).")

Ks = np.arange(1, 61)
gl_err = np.array([abs(gregory_leibniz(int(K) - 1) - np.pi) for K in Ks])
ma_err = np.array([max(abs(machin(int(K)) - np.pi), 1e-17) for K in Ks])
plt.figure(figsize=(7.5, 4.5))
plt.semilogy(Ks, gl_err, 'b.-', ms=4, label='Gregory–Leibniz')
plt.semilogy(Ks, ma_err, 'r.-', ms=4, label='Machin formula')
plt.xlabel('number of terms K'); plt.ylabel('|error|')
plt.title('Convergence to pi (logarithmic error axis)')
plt.legend(); plt.grid(True, which='both', alpha=0.3)
plt.tight_layout()

# ── D. ∫_0^1 sin(x²) dx via a power series — error per order ────────────────
print()
print("D. ∫_0^1 sin(x²) dx  —  power series versus scipy.quad")
print("-" * 66)
# sin(x²) = Sum (-1)^k x^(4k+2)/(2k+1)!  ->  ∫_0^1 = Sum (-1)^k / ((4k+3)(2k+1)!)
qv, qerr = quad(lambda t: np.sin(t**2), 0, 1)
print(f"   scipy.quad = {qv:.12f}   (est. error {qerr:.1e})")
print()
print(f"   {'terms K':>7s} {'order x^(4K-2)':>14s} {'approximation':>16s} {'|error|':>12s}")
partial = 0.0
for K in range(1, 8):
    k = K - 1
    partial += (-1)**k / ((4 * k + 3) * math.factorial(2 * k + 1))
    print(f"   {K:7d} {4*K - 2:14d} {partial:16.12f} {abs(partial - qv):12.2e}")
print("   Each extra term gains about two decimal digits: with 5 terms")
print("   we are at ~1e-9 and with 7 at the limits of double precision.")

# Comparison with SymPy's symbolic value
sym = sp.integrate(sp.sin(x**2), (x, 0, 1))
print(f"   SymPy symbolically: {sym}")
print(f"   numerically       : {float(sym.evalf()):.12f}   (0.310268301723)")
plt.show()
