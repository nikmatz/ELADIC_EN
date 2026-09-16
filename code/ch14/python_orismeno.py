# ============================================================
# python_orismeno.py
# Chapter 14 — Definite Integral: Riemann Sums
# Matzakos, N. (2026). Elements of Linear Algebra, Differential & Integral Calculus. NewTech Publications.
# ============================================================
#
# LIBRARIES:
#   numpy       → vectorized Riemann sums (fast, no loops)
#   sympy       → symbolic sum and limit (from the definition)
#   scipy       → reference numerical integration
#   matplotlib  → bar, fill_between, loglog
#
# BASIC COMMANDS:
#   numpy.linspace(a, b, n+1)     → partition of [a,b]
#   numpy.sum(f(x)) * dx          → Riemann sum
#   sympy.summation(expr,(i,1,n)) → closed form of the sum
#   sympy.limit(expr, n, oo)      → limit as n → ∞
#   matplotlib.bar()              → Riemann rectangles
#   matplotlib.fill_between()     → shading of a region
#
# Book activity:
#   (a) riemann(f,a,b,n,rule) for f(x)=x² on [0,2], n=4,10,10²,10⁴
#   (b) visualization of the rectangles for n=4 and n=20
#   (c) rate of convergence on a log-log plot
#   (d) symbolically from the definition (sympy.summation, sympy.limit)
#   (e) properties: linearity, additivity, reversal, symmetries
#   (f) bounds for e^(x²) on [0,1] and tightening them
#   (g) average value of x² on [0,3] with fill_between
# ============================================================

import numpy as np
import sympy as sp
import matplotlib.pyplot as plt
from scipy.integrate import quad

print("=" * 62)
print(" Chapter 14: Definite Integral — Riemann Sums")
print("=" * 62)

EXACT = 8/3          # the exact value of ∫₀² x² dx


# ── A. (a) The function riemann(f, a, b, n, rule) ───────
def riemann(f, a, b, n, rule='left'):
    """Riemann sum of f on [a,b] with n subintervals.

    rule = 'left'  → left endpoints    x_(i-1)
    rule = 'mid'   → midpoints         (x_(i-1)+x_i)/2
    rule = 'right' → right endpoints   x_i
    Implemented with numpy (vectorized) — it handles n = 10^4 with ease.
    """
    edges = np.linspace(a, b, n + 1)
    dx = (b - a)/n
    if rule == 'left':
        pts = edges[:-1]
    elif rule == 'right':
        pts = edges[1:]
    elif rule == 'mid':
        pts = (edges[:-1] + edges[1:])/2
    else:
        raise ValueError("rule ∈ {'left', 'mid', 'right'}")
    return float(np.sum(f(pts)) * dx)


f = lambda z: z**2

print("\n──── A. (a) riemann(f, a, b, n, rule) for f(x)=x² on [0,2] ────")
print(f"  Exact value: ∫₀²x²dx = 8/3 = {EXACT:.10f}")
print(f"\n  {'n':>7} {'left':>14} {'mid':>14} {'right':>14}"
      f" {'|mid-8/3|':>12}")
for n in (4, 10, 10**2, 10**4):
    L = riemann(f, 0, 2, n, 'left')
    M = riemann(f, 0, 2, n, 'mid')
    R = riemann(f, 0, 2, n, 'right')
    print(f"  {n:>7d} {L:>14.8f} {M:>14.8f} {R:>14.8f} {abs(M-EXACT):>12.2e}")

print("\n  Check L_n < 8/3 < R_n for every n:")
for n in (4, 10, 10**2, 10**4):
    L = riemann(f, 0, 2, n, 'left')
    R = riemann(f, 0, 2, n, 'right')
    print(f"    n = {n:>6d}: {L:.8f} < {EXACT:.8f} < {R:.8f}  →  "
          f"{L < EXACT < R}")

# ── B. (b) Visualization of the Riemann rectangles ───────
print("\n──── B. (b) The Riemann rectangles for n = 4 and n = 20 ────")

fig, axes = plt.subplots(1, 2, figsize=(11.5, 4.4))
fig.suptitle("Riemann sums for f(x) = x² on [0,2]  —  "
             "as n grows, the rectangles fill the region",
             fontsize=11, fontweight='bold')

for ax, n in zip(axes, (4, 20)):
    edges = np.linspace(0, 2, n + 1)
    dx = 2/n
    ax.bar(edges[:-1], f(edges[1:]), width=dx, align='edge',
           color='steelblue', edgecolor='white', alpha=.55,
           label=f'right endpoints (n={n})')
    ax.bar(edges[:-1], f(edges[:-1]), width=dx, align='edge',
           color='none', edgecolor='darkorange', lw=1.2,
           label=f'left endpoints (n={n})')
    zz = np.linspace(0, 2, 400)
    ax.plot(zz, f(zz), 'r-', lw=2.2, label='f(x) = x²')
    L = riemann(f, 0, 2, n, 'left'); R = riemann(f, 0, 2, n, 'right')
    ax.set_title(f"n = {n}:  L_n = {L:.4f},  R_n = {R:.4f}", fontsize=10)
    ax.set_xlabel("x"); ax.legend(fontsize=8); ax.grid(alpha=.3)
    print(f"  n = {n:2d}: L_n = {L:.6f},  R_n = {R:.6f},  "
          f"gap between the bounds R_n - L_n = {R-L:.6f}")

plt.tight_layout()

# ── C. (c) Rate of convergence — log-log plot ──────────
print("\n──── C. (c) Rate of convergence (log-log) ────")

ns = np.array([2**k for k in range(2, 15)])          # 4 … 16384
errors = {}
for rule in ('left', 'mid', 'right'):
    errors[rule] = np.array([abs(riemann(f, 0, 2, int(n), rule) - EXACT)
                             for n in ns])

plt.figure(figsize=(7.2, 5))
styles = {'left': ('o-', 'darkorange'), 'mid': ('s-', 'seagreen'),
          'right': ('^-', 'steelblue')}
for rule in ('left', 'mid', 'right'):
    mk, col = styles[rule]
    plt.loglog(ns, errors[rule], mk, color=col, ms=4, lw=1.4,
               label=f"{rule}")
# Reference lines of slope -1 and -2
plt.loglog(ns, 4.0/ns, 'k--', lw=1, alpha=.6, label='reference ~ 1/n')
plt.loglog(ns, 4.0/ns**2, 'k:', lw=1.2, alpha=.8, label='reference ~ 1/n²')
plt.xlabel("n (number of subintervals)")
plt.ylabel("|S_n - 8/3|")
plt.title("Rate of convergence of the three rules (log-log)")
plt.legend(fontsize=9); plt.grid(alpha=.3, which='both')
plt.tight_layout()

print("  Slope of the line on the log-log plot (= -p, where error ~ n^(-p)):")
for rule in ('left', 'mid', 'right'):
    slope = np.polyfit(np.log(ns), np.log(errors[rule]), 1)[0]
    print(f"    {rule:>5s}: slope = {slope:+.4f}  →  error ~ n^({slope:.2f})"
          f"   [order p ≈ {abs(slope):.0f}]")
print("  ⇒ left/right converge like 1/n, mid like 1/n².")

# ── D. (d) Symbolically, from the definition ────────────
print("\n──── D. (d) Symbolically from the definition (no antiderivative) ────")

i = sp.symbols('i', integer=True, positive=True)
n = sp.symbols('n', integer=True, positive=True)

# dx = 2/n, right endpoints x_i = 2i/n
R_n = sp.factor(sp.simplify(sp.summation((2*i/n)**2 * (2/n), (i, 1, n))))
L_n = sp.factor(sp.simplify(sp.summation((2*(i-1)/n)**2 * (2/n), (i, 1, n))))
M_n = sp.factor(sp.simplify(sp.summation(((2*i-1)/n)**2 * (2/n), (i, 1, n))))

print(f"  Sum i² = {sp.factor(sp.summation(i**2, (i, 1, n)))}")
print(f"  R_n = {R_n}")
print(f"  L_n = {L_n}")
print(f"  M_n = {M_n}")
print(f"  lim R_n = {sp.limit(R_n, n, sp.oo)}   [EXPECTED 8/3]")
print(f"  lim L_n = {sp.limit(L_n, n, sp.oo)}")
print(f"  lim M_n = {sp.limit(M_n, n, sp.oo)}")

xs_ = sp.symbols('x')
print(f"  Verification with sympy.integrate: "
      f"∫₀²x²dx = {sp.integrate(xs_**2, (xs_, 0, 2))}")

# ── E. (e) Properties — numerical verification ──────────
print("\n──── E. (e) Properties of the definite integral ────")

Q = lambda g, a, b: quad(g, a, b)[0]      # numerical ∫_a^b g

# Linearity
lhs = Q(lambda z: 3*z**2 + 5*np.sin(z), 0, 1)
rhs = 3*Q(lambda z: z**2, 0, 1) + 5*Q(np.sin, 0, 1)
print(f"  Linearity  : ∫₀¹(3x²+5sin x) = {lhs:.12f}")
print(f"               3∫₀¹x² + 5∫₀¹sin x = {rhs:.12f}"
      f"   |difference| = {abs(lhs-rhs):.2e}")

# Additivity over intervals
whole = Q(lambda z: z**2, 0, 3)
split = Q(lambda z: z**2, 0, 1) + Q(lambda z: z**2, 1, 3)
print(f"  Additivity : ∫₀³x² = {whole:.12f} ,  ∫₀¹+∫₁³ = {split:.12f}"
      f"   |difference| = {abs(whole-split):.2e}")

# Reversal of the limits
fwd = Q(lambda z: z**2, 1, 4)
bwd = Q(lambda z: z**2, 4, 1)
print(f"  Reversal   : ∫₁⁴x² = {fwd:.12f} ,  ∫₄¹x² = {bwd:.12f}"
      f"   sum = {fwd+bwd:.2e}")

# Symmetries
odd = Q(lambda z: z**3, -2, 2)
even_full = Q(lambda z: z**2, -2, 2)
even_half = 2*Q(lambda z: z**2, 0, 2)
print(f"  Odd        : ∫₋₂²x³ = {odd:.2e}   [EXPECTED 0]")
print(f"  Even       : ∫₋₂²x² = {even_full:.12f} ,  "
      f"2∫₀²x² = {even_half:.12f}   |difference| = {abs(even_full-even_half):.2e}")

# ── F. (f) Bounds for f(x) = e^(x²) on [0,1] ───────────
print("\n──── F. (f) Bounds for f(x) = e^(x²) on [0,1] ────")

g = lambda z: np.exp(z**2)
I_exact = Q(g, 0, 1)
print(f"  ∫₀¹ e^(x²) dx = {I_exact:.12f}   (quad)")
print(f"  f is increasing on [0,1] (f' = 2x·e^(x²) ≥ 0),")
print(f"  so m = f(0) = {g(0.0):.6f} and M = f(1) = e = {g(1.0):.6f}.")
print(f"  Crude bound: {g(0.0):.6f} ≤ ∫ ≤ {g(1.0):.6f}   →  "
      f"{g(0.0) <= I_exact <= g(1.0)}")

print("\n  Tightening by splitting [0,1] into k equal subintervals")
print("  (on each one m_j = f(left endpoint), M_j = f(right endpoint)):")
print(f"  {'k':>3} {'lower bound':>16} {'upper bound':>16} {'width':>12}"
      f" {'contains the integral?':>24}")
for k in (1, 2, 4, 8):
    e_ = np.linspace(0, 1, k + 1)
    h = 1/k
    lower = float(np.sum(g(e_[:-1])) * h)     # f increasing ⇒ min at the left
    upper = float(np.sum(g(e_[1:])) * h)      #               max at the right
    print(f"  {k:>3d} {lower:>16.10f} {upper:>16.10f} {upper-lower:>12.6f}"
          f" {str(lower <= I_exact <= upper):>24s}")

print("\n  Comparison: on [0,1] we have x² ≤ x, so e^(x²) ≤ e^x.")
I_ex = Q(np.exp, 0, 1)
print(f"    ∫₀¹e^(x²)dx = {I_exact:.12f}   ≤   ∫₀¹e^x dx = {I_ex:.12f}"
      f"   →  {I_exact <= I_ex}")

# ── G. (g) Average value of f(x) = x² on [0,3] ──────────
print("\n──── G. (g) Average value of f(x) = x² on [0,3] ────")

N_big = 10**4
I_riem = riemann(f, 0, 3, N_big, 'mid')
fbar = I_riem / (3 - 0)
print(f"  ∫₀³x²dx ≈ {I_riem:.10f} (midpoint Riemann sum, n = {N_big})"
      f"   [exact: 9]")
print(f"  Average value f̄ = ∫₀³f/(b-a) ≈ {fbar:.10f}   [EXPECTED 3]")

xi = np.sqrt(fbar)
print(f"  MVT: f(c) = f̄  ⇒  c = √f̄ ≈ {xi:.10f}   [EXPECTED √3 ≈ "
      f"{np.sqrt(3):.10f}]")
print(f"  Area of the rectangle f̄·(b-a) = {fbar*3:.10f}  versus  "
      f"∫₀³f = {I_riem:.10f}   |difference| = {abs(fbar*3 - I_riem):.2e}")

zz = np.linspace(0, 3, 400)
plt.figure(figsize=(7.5, 5))
plt.fill_between(zz, 0, f(zz), color='steelblue', alpha=.35,
                 label="region under f(x)=x²   (area = 9)")
plt.fill_between([0, 3], 0, [fbar, fbar], color='crimson', alpha=.18,
                 label=f"rectangle of height f̄ = {fbar:.4f}  "
                       f"(area = {fbar*3:.4f})")
plt.plot(zz, f(zz), 'b-', lw=2.2)
plt.axhline(fbar, color='crimson', lw=2, ls='--')
plt.plot([xi], [fbar], 'ko', ms=8, zorder=5)
plt.annotate(f"c ≈ {xi:.4f}", (xi, fbar), textcoords="offset points",
             xytext=(10, -18), fontsize=10)
plt.vlines(xi, 0, fbar, color='k', ls=':', lw=1.2)
plt.xlabel("x"); plt.ylabel("y"); plt.xlim(0, 3); plt.ylim(0, 9.5)
plt.title("Average value: the two areas are equal (Mean Value Theorem)")
plt.legend(fontsize=9, loc='upper left'); plt.grid(alpha=.3)
plt.tight_layout()

print("\n✓ Chapter 14 completed.")
plt.show()
