# ============================================================
# python_efarm_par.py
# Chapter 12 — Applications of the Derivative: SymPy & SciPy
# Matzakos, N. (2026). Elements of Linear Algebra, Differential & Integral Calculus. NewTech Publications.
# ============================================================
#
# LIBRARIES:
#   sympy  → limits (L'Hôpital), critical points
#   scipy  → optimize.minimize_scalar, optimize.newton
#   numpy / matplotlib → convergence and optimization plots
#
# BASIC COMMANDS:
#   sympy.limit(f, x, a)                  → limit (dir='+' for one-sided)
#   sympy.solve(diff(f, x), x)            → critical points
#   scipy.optimize.minimize_scalar(f, ...)→ numerical minimization
#   scipy.optimize.newton(f, x0, fprime)  → numerical root (Newton)
# ============================================================

import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import minimize_scalar, newton
from sympy import (symbols, diff, limit, solve, simplify, lambdify, together,
                   fraction, exp, log, sin, oo, nan, zoo, S)

x = symbols('x')

print("=" * 58)
print(" Chapter 12: Applications of the Derivative — Python")
print("=" * 58)

# ── A. L'Hôpital's Rule — step by step ────────────────
print("\n── A. L'Hôpital's Rule ──")

INDET = (S.Zero, oo, -oo, zoo, nan)


def _form(num, den, pt, direction):
    """Returns (limit of numerator, limit of denominator) at the point pt."""
    ln = limit(num, x, pt, direction)
    ld = limit(den, x, pt, direction)
    return ln, ld


def _is_indeterminate(ln, ld):
    """0/0 or ±oo/±oo ?"""
    zero_zero = (ln == 0 and ld == 0)
    inf_inf = (ln in (oo, -oo, zoo) and ld in (oo, -oo, zoo))
    return zero_zero or inf_inf


def lhopital(num, den, pt, direction='+-', max_steps=5, label=""):
    """Applies L'Hôpital step by step and prints every intermediate step."""
    print(f"\n  {label}")
    ln, ld = _form(num, den, pt, direction)
    print(f"    Step 0: ({num}) / ({den})")
    print(f"            numerator → {ln},  denominator → {ld}")
    if not _is_indeterminate(ln, ld):
        val = limit(num/den, x, pt, direction)
        print(f"            not an indeterminate form; value = {val}")
        return val
    form = "0/0" if ln == 0 else "±oo/±oo"
    print(f"            indeterminate form {form} → we apply L'Hôpital")

    n_k, d_k = num, den
    for k in range(1, max_steps + 1):
        n_raw, d_raw = diff(n_k, x), diff(d_k, x)
        print(f"    Step {k}: ({n_raw}) / ({d_raw})")
        # Algebraic rearrangement of the quotient — otherwise forms such as
        # (1/x)/(-1/x^2) would stay "oo/oo" forever.
        n_k, d_k = fraction(together(simplify(n_raw/d_raw)))
        if (n_k, d_k) != (n_raw, d_raw):
            print(f"            after simplification: ({n_k}) / ({d_k})")
        ln, ld = _form(n_k, d_k, pt, direction)
            print(f"            numerator → {ln},  denominator → {ld}")
        if not _is_indeterminate(ln, ld):
            val = limit(n_k/d_k, x, pt, direction)
            print(f"            the indeterminacy is RESOLVED · limit = {val}")
            return val
        form = "0/0" if ln == 0 else "±oo/±oo"
        print(f"            again {form} → we continue")
    print(f"    Not resolved in {max_steps} steps.")
    return None


# (1) lim_{x→0} (e^x - 1 - x)/x^2      [0/0]  → 1/2
v1 = lhopital(exp(x) - 1 - x, x**2, 0,
              label="(1) lim_(x→0) (e^x - 1 - x)/x^2      [form 0/0]")
d1 = limit((exp(x) - 1 - x)/x**2, x, 0)
print(f"    sympy.limit = {d1}   (expected 1/2)   L'Hôpital step by step: {v1}"
      f"   agreement: {simplify(v1 - d1) == 0}")

# (2) lim_{x→0+} x·ln x                [0·(-oo)] → 0
print("\n  (2) lim_(x→0+) x·ln(x)      [form 0 · (-oo)]")
print(f"    x → {limit(x, x, 0, '+')},  ln(x) → {limit(log(x), x, 0, '+')}")
print("    Rewriting as a quotient: x·ln x = ln(x) / (1/x)   [form -oo/oo]")
v2 = lhopital(log(x), 1/x, 0, direction='+',
              label="(2b) lim_(x→0+) ln(x)/(1/x)")
d2 = limit(x*log(x), x, 0, '+')
print(f"    sympy.limit = {d2}   (expected 0)   L'Hôpital step by step: {v2}"
      f"   agreement: {simplify(v2 - d2) == 0}")

# (3) lim_{x→+oo} x^2/e^x              [oo/oo] → 0
v3 = lhopital(x**2, exp(x), oo,
              label="(3) lim_(x→+oo) x^2/e^x      [form oo/oo]")
d3 = limit(x**2/exp(x), x, oo)
print(f"    sympy.limit = {d3}   (expected 0)   L'Hôpital step by step: {v3}"
      f"   agreement: {simplify(v3 - d3) == 0}")
print("    Interpretation: e^x dominates every polynomial.")

# (4) lim_{x→0} (1/x - 1/sin x)        [oo - oo] → 0
print("\n  (4) lim_(x→0) (1/x - 1/sin x)      [form oo - oo]")
expr4 = 1/x - 1/sin(x)
num4, den4 = fraction(together(expr4))
print(f"    Common denominator: ({num4}) / ({den4})")
v4 = lhopital(num4, den4, 0, label="(4b) lim_(x→0) (sin x - x)/(x·sin x)")
d4 = limit(expr4, x, 0)
print(f"    sympy.limit = {d4}   (expected 0)   L'Hôpital step by step: {v4}"
      f"   agreement: {simplify(v4 - d4) == 0}")

# ── B. Optimization: rectangle of perimeter P = 20 ──────
print("\n── B. Rectangle of perimeter P=20: E(x) = x(10-x) ──")

E = x*(10 - x)
dE = diff(E, x)
sol_E = solve(dE, x)
xE = sol_E[0]
print(f"  E'(x) = {dE},  E'(x)=0 → x = {sol_E}   (expected [5])")
print(f"  E''(x) = {diff(E, x, 2)} < 0 → MAXIMUM")
print(f"  E_max = E({xE}) = {E.subs(x, xE)}   (expected 25 — a 5×5 square)")

# Numerical verification: we minimize -E
E_num = lambdify(x, E, 'numpy')
resE = minimize_scalar(lambda t: -E_num(t), bounds=(0, 10), method='bounded')
print(f"  scipy.minimize_scalar(-E): x = {resE.x:.8f}, E = {-resE.fun:.8f}")
print(f"  Deviation from x=5: {abs(resE.x - float(xE)):.2e}")

# ── C. Open box V=32: S(x) = x^2 + 128/x ────────────
print("\n── C. Open box (no lid) V=32 ──")

xp = symbols('x', positive=True)
h_box = 32/xp**2                      # height from the volume: x^2·h = 32
S_expr = (xp**2 + 4*xp*h_box).expand()  # base + 4 sides (no lid)
print(f"  height h = 32/x²,  S(x) = x² + 4xh = {S_expr}")
print(f"  Identical to x² + 128/x: "
      f"{simplify(S_expr - (xp**2 + 128/xp)) == 0}")

dS = simplify(diff(S_expr, xp))
sol_S = [s for s in solve(dS, xp) if s.is_real and s > 0]
xS = sol_S[0]
print(f"  S'(x) = {dS}")
print(f"  S'(x)=0 → x = {sol_S}   (expected [4])")
print(f"  S''(x) = {simplify(diff(S_expr, xp, 2))},  "
      f"S''({xS}) = {diff(S_expr, xp, 2).subs(xp, xS)} > 0 → MINIMUM")
print(f"  S_min = S({xS}) = {S_expr.subs(xp, xS)}   (expected 48)")
print(f"  height h = {h_box.subs(xp, xS)}   (expected 2)")
print(f"  Volume check: x²·h = {(xp**2*h_box).subs(xp, xS)}   (expected 32)")

S_num = lambdify(xp, S_expr, 'numpy')
resS = minimize_scalar(S_num, bounds=(0.5, 20), method='bounded')
print(f"  scipy.minimize_scalar(S): x = {resS.x:.8f}, S = {resS.fun:.8f}")
print(f"  Deviation from x=4: {abs(resS.x - float(xS)):.2e}")

xs_S = np.linspace(1.0, 12.0, 500)
plt.figure(figsize=(7, 4.5))
plt.plot(xs_S, S_num(xs_S), 'b-', lw=2.2, label=r"$S(x)=x^2+\dfrac{128}{x}$")
plt.scatter([float(xS)], [float(S_expr.subs(xp, xS))], color='red', s=90,
            zorder=5, label=f"minimum: x={xS}, S={S_expr.subs(xp, xS)}")
plt.axvline(float(xS), color='0.6', lw=0.9, ls=':')
plt.axhline(float(S_expr.subs(xp, xS)), color='0.6', lw=0.9, ls=':')
plt.ylim(0, 250); plt.grid(alpha=0.3); plt.legend()
plt.xlabel('base side x'); plt.ylabel('surface area S')
plt.title("Open box V=32: minimum surface area")
plt.tight_layout()

# ── D. Newton-Raphson: x^3 - x - 2 = 0, x0 = 1.5 ──────────
print("\n── D. Newton-Raphson for x³ - x - 2 = 0 (x₀ = 1.5) ──")

fN_sym = x**3 - x - 2
dfN_sym = diff(fN_sym, x)
fN = lambdify(x, fN_sym, 'numpy')
dfN = lambdify(x, dfN_sym, 'numpy')
print(f"  f(x) = {fN_sym},  f'(x) = {dfN_sym}")

# Reference root with scipy
root_scipy, info = newton(fN, x0=1.5, fprime=dfN, tol=1e-14, full_output=True)
print(f"  scipy.optimize.newton: root = {root_scipy:.13f}  "
      f"({info.iterations} iterations)")
print(f"  f(root) = {fN(root_scipy):.3e}")

x0 = 1.5
iterates = [x0]
errors = [abs(x0 - root_scipy)]
print("\n  i        x_i                   f(x_i)          |x_i - root|   "
      "correct digits")
print(f"  0   {x0:.13f}   {fN(x0):+.6e}   {errors[0]:.3e}")
xi = x0
for i in range(1, 6):
    xi = xi - fN(xi)/dfN(xi)
    err = abs(xi - root_scipy)
    iterates.append(xi)
    errors.append(err)
    digits = (f"{-np.log10(err):5.1f}" if err > 0 else " (exact)")
    print(f"  {i}   {xi:.13f}   {fN(xi):+.6e}   {err:.3e}   {digits}")

print(f"\n  Root (Newton, 5 steps): {iterates[-1]:.13f}")
print(f"  Root (scipy.newton):    {root_scipy:.13f}")
print(f"  Difference: {abs(iterates[-1] - root_scipy):.3e}")
print("  Expected root: 1.5213797068046")
print("  Quadratic convergence: the number of correct decimal digits")
print("  roughly doubles at each step (≈3.4 → 7.0 → 14.1).")

# Convergence plot: tangent lines and successive approximations
fig, axes = plt.subplots(1, 2, figsize=(12, 4.8))

ax = axes[0]
xs_N = np.linspace(1.2, 1.75, 400)
ax.plot(xs_N, fN(xs_N), 'b-', lw=2.2, label=r"$f(x)=x^3-x-2$")
ax.axhline(0, color='k', lw=0.8)
cols = ['#d62728', '#ff7f0e', '#2ca02c', '#9467bd']
for k in range(min(3, len(iterates) - 1)):
    xk = iterates[k]
    yk = fN(xk)
    # tangent at (x_k, f(x_k)) — it meets the axis at x_{k+1}
    tang = yk + dfN(xk)*(xs_N - xk)
    ax.plot(xs_N, tang, '--', lw=1.2, color=cols[k],
            label=f"tangent at $x_{k}$ = {xk:.6f}")
    ax.plot([xk, xk], [0, yk], ':', lw=1, color=cols[k])
    ax.scatter([xk], [yk], color=cols[k], s=45, zorder=5)
    ax.scatter([iterates[k + 1]], [0], color=cols[k], s=45, marker='v', zorder=5)
ax.scatter([root_scipy], [0], color='k', s=80, marker='*', zorder=6,
           label=f"root ≈ {root_scipy:.7f}")
ax.set_ylim(-0.6, 1.2); ax.set_xlim(1.2, 1.75)
ax.grid(alpha=0.3); ax.legend(fontsize=8); ax.set_xlabel('x')
ax.set_title("Newton: each tangent gives the next approximation")

ax = axes[1]
nz = [(i, e) for i, e in enumerate(errors) if e > 0]
ax.semilogy([i for i, _ in nz], [e for _, e in nz], 'o-', lw=2, color='crimson')
for i, e in nz:
    ax.annotate(f"{e:.1e}", (i, e), textcoords="offset points",
                xytext=(6, 6), fontsize=8)
ax.set_xlabel('iteration i'); ax.set_ylabel(r'$|x_i - r|$  (logarithmic)')
ax.grid(alpha=0.3, which='both')
ax.set_title("Error on a semi-logarithmic scale\n(the curvature ⇒ quadratic convergence)")

plt.tight_layout()
plt.show()

print("\nChapter 12 completed.")
