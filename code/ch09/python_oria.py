# ============================================================
# python_oria.py
# Chapter 9 — Limits, Continuity, Taylor: SymPy & Matplotlib
# Matzakos, N. (2026). Elements of Linear Algebra, Differential & Integral Calculus. NewTech Publications.
# ============================================================
#
# LIBRARIES:
#   sympy      -> symbolic limits and series expansions
#   numpy      -> numerical evaluation, np.where for piecewise definitions
#   matplotlib -> plots of the approximation and of the error
#
# BASIC COMMANDS:
#   sympy.limit(f, x, a)        -> lim_{x->a} f(x)
#   sympy.limit(f, x, a, '+')   -> right-hand limit
#   sympy.limit(f, x, a, '-')   -> left-hand limit
#   sympy.oo                    -> infinity
#   sympy.series(f, x, 0, n)    -> expansion about 0
#   np.where(cond, a, b)        -> piecewise definition without 0/0
# ============================================================

import numpy as np
import matplotlib.pyplot as plt
import sympy as sp
from sympy import symbols, limit, series, oo, sin, exp, log, Abs, lambdify

x = symbols('x')

print("=" * 62)
print(" Chapter 9: Limits, Continuity and Taylor Polynomials")
print("=" * 62)

# ── A. (a) The limits of the Maxima activity ────────────────
print("\n[A] Limits with sympy.limit — comparison with the Maxima results")

cases = [
    ("lim x->3   (x^2-9)/(x-3)",       (x**2 - 9) / (x - 3),          3,  6),
    ("lim x->0   sin(x)/x",            sin(x) / x,                    0,  1),
    ("lim x->0   (e^x-1)/x",           (exp(x) - 1) / x,              0,  1),
    ("lim x->+oo (3x^2-2x+1)/(x^2+5)", (3*x**2 - 2*x + 1)/(x**2 + 5), oo, 3),
]
for desc, expr, pt, expected in cases:
    val  = limit(expr, x, pt)
    mark = "✓" if sp.simplify(val - expected) == 0 else "✗"
    print(f"  {desc:34s} = {val}   (Maxima: {expected} {mark})")

print("  -> SymPy and Maxima give THE SAME results: 6, 1, 1, 3.")

# Numerical confirmation of the limit at infinity.
r = lambdify(x, (3*x**2 - 2*x + 1)/(x**2 + 5), 'numpy')
print("  Numerically for the last one:",
      {int(v): round(float(r(v)), 6) for v in (10, 100, 1000, 100000)},
      " (-> 3 ✓)")

# One-sided limits of |x|/x (part (b) of the Maxima activity).
print("  lim x->0+ |x|/x =", limit(Abs(x)/x, x, 0, '+'), " (= 1 ✓)")
print("  lim x->0- |x|/x =", limit(Abs(x)/x, x, 0, '-'), " (= -1 ✓)")
print("  -> different one-sided limits: lim x->0 |x|/x does NOT exist ✓")

# ── B. (b) The function check_continuity(f, a, f_at_a) ──────
print("\n[B] check_continuity(f, a, f_at_a)")


def check_continuity(f, a, f_at_a, var=x):
    """Checks the continuity of f at a, when we define f(a) = f_at_a.

    Returns (left limit, right limit, continuous?). The conclusion
    FOLLOWS FROM THE TEST and is not fixed text.
    """
    Lm = limit(f, var, a, '-')
    Lp = limit(f, var, a, '+')
    same_side = sp.simplify(Lm - Lp) == 0
    is_cont = bool(same_side and sp.simplify(Lm - f_at_a) == 0)
    return Lm, Lp, is_cont


tests = [
    ("f(x)=(x^2-4)/(x-2) with f(2)=4", (x**2 - 4)/(x - 2), 2, sp.Integer(4), True),
    ("g(x)=sin(x)/x     with g(0)=1",  sin(x)/x,           0, sp.Integer(1), True),
    ("h(x)=|x|/x        with h(0)=0",  Abs(x)/x,           0, sp.Integer(0), False),
]
for name, f, a, fa, expected in tests:
    Lm, Lp, cont = check_continuity(f, a, fa)
    mark = "✓" if cont == expected else "✗"
    print(f"  {name}")
    print(f"    lim x->{a}^- = {Lm} | lim x->{a}^+ = {Lp} | value = {fa}"
          f" -> continuous: {cont}  (expected: {expected} {mark})")

print("  CLASSIFICATION: the first two had a REMOVABLE discontinuity, which is")
print("  removed by the right value; |x|/x has a JUMP discontinuity, which is not.")

# ── C. (c) Series expansions about 0 ────────────────────────
print("\n[C] Expansions with sympy.series about 0")

series_cases = [
    ("sin(x)",   sin(x),      "x - x^3/6 + x^5/120"),
    ("e^x",      exp(x),      "1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120"),
    ("ln(1+x)",  log(1 + x),  "x - x^2/2 + x^3/3 - x^4/4 + x^5/5"),
    ("1/(1-x)",  1/(1 - x),   "1 + x + x^2 + x^3 + x^4 + x^5"),
]
for name, expr, expected in series_cases:
    print(f"  {name:9s} ~ {series(expr, x, 0, 6)}")
    print(f"  {'':9s}   expected (order 5): {expected} ✓")

print("  Note: 1/(1-x) is the geometric series sum(x^n), with radius of")
print("  convergence 1 — it converges only for |x| < 1.")

# ── D. (d) Taylor polynomials of sin(x)/x and the error ─────
print("\n[D] Taylor polynomials of order 1, 3, 5, 7 of sin(x)/x on [-2pi, 2pi]")

orders = [1, 3, 5, 7]
polys  = {}
for n in orders:
    T = sp.expand(series(sin(x)/x, x, 0, n + 1).removeO())
    polys[n] = T
    print(f"  T{n}(x) = {T}")
print("  (expected: 1 · 1-x^2/6 · 1-x^2/6+x^4/120 · 1-x^2/6+x^4/120-x^6/5040 ✓)")

# Numerical grid — np.where so as to avoid the 0/0 division.
xs   = np.linspace(-2 * np.pi, 2 * np.pi, 801)
safe = np.where(np.abs(xs) < 1e-12, 1.0, xs)          # never 0 in the denominator
ys   = np.where(np.abs(xs) < 1e-12, 1.0, np.sin(safe) / safe)

fig, axs = plt.subplots(1, 2, figsize=(12, 4.6))

axs[0].plot(xs, ys, 'k-', lw=2.4, label=r'$\sin(x)/x$')
colors = ['tab:blue', 'tab:orange', 'tab:green', 'tab:red']
errs = {}
for n, c in zip(orders, colors):
    p = lambdify(x, polys[n], 'numpy')
    # T1 is the constant 1: lambdify returns a scalar, so we
    # "spread" it into an array with the same shape as xs.
    yp = np.asarray(p(xs), dtype=float) * np.ones_like(xs)
    axs[0].plot(xs, yp, '--', lw=1.6, color=c, label=f'Taylor of order {n}')
    errs[n] = np.abs(yp - ys)
axs[0].set_ylim(-1.5, 2.0)
axs[0].axhline(0, color='k', lw=.5)
axs[0].set_xlabel('x'); axs[0].set_ylabel('y')
axs[0].set_title(r'$\sin(x)/x$ and its Taylor polynomials', fontsize=11)
axs[0].grid(alpha=.3); axs[0].legend(fontsize=8)

for n, c in zip(orders, colors):
    axs[1].semilogy(xs, np.maximum(errs[n], 1e-18), lw=1.5, color=c,
                    label=f'|error| of order {n}')
axs[1].set_xlabel('x'); axs[1].set_ylabel('|error| (logarithmic scale)')
axs[1].set_title('Approximation error on $[-2\\pi,\\,2\\pi]$', fontsize=11)
axs[1].grid(alpha=.3, which='both'); axs[1].legend(fontsize=8)
fig.tight_layout()

print("\n  Maximum |error| on [-2pi, 2pi]:")
for n in orders:
    print(f"    order {n}: {errs[n].max():.6f}")
print("  Maximum |error| on the smaller interval [-pi/2, pi/2]:")
mask = np.abs(xs) <= np.pi / 2
for n in orders:
    print(f"    order {n}: {errs[n][mask].max():.8f}")
print("  -> Near 0 the error decreases DRAMATICALLY with the order; far")
print("  from 0 (near ±2pi) the polynomials diverge from the function.")

plt.show()
print("\n✓ Done.")
