# ============================================================
# python_akrotata.py
# Chapter 11 — Monotonicity and Extrema, SymPy & Matplotlib
# Matzakos, N. (2026). Elements of Linear Algebra, Differential & Integral Calculus. NewTech Publications.
# ============================================================
#
# LIBRARIES:
#   sympy       -> critical points, second derivative test
#   numpy       -> sign table on a dense grid (np.sign)
#   matplotlib  -> plots, shading of intervals (axvspan)
#
# BASIC COMMANDS:
#   sympy.solve(diff(f,x), x)   -> critical points
#   sympy.diff(f, x, 2)         -> second derivative
#   sympy.lambdify(x, f)        -> symbolic -> numerical
#   np.sign(...)                -> sign on a dense grid
#   ax.axvspan(a, b, ...)       -> shading of an interval
# ============================================================

import numpy as np
import matplotlib.pyplot as plt
from sympy import symbols, diff, solve, simplify, lambdify, sqrt, limit

x = symbols('x', real=True)

print("=" * 58)
print(" Chapter 11: Monotonicity, Extrema, Convexity — Python")
print("=" * 58)

# The function from the book
f  = x**3 - 3*x**2 - 9*x + 5
f1 = diff(f, x)
f2 = diff(f, x, 2)

print(f"\nf(x)   = {f}")
print(f"f'(x)  = {f1}")
print(f"f''(x) = {f2}")

# ── A. Critical points — second derivative test ───────────
print("\n── A. Critical points and the second derivative test ──")

crits = sorted(solve(f1, x))
print(f"  Critical points (f'=0): x = {crits}   (expected [-1, 3])")

kinds = {}
for xi in crits:
    yi  = f.subs(x, xi)
    f2i = f2.subs(x, xi)
    if f2i > 0:
        kind = "local MINIMUM"
    elif f2i < 0:
        kind = "local MAXIMUM"
    else:
        kind = "inconclusive (another test is needed)"
    kinds[xi] = kind
    print(f"    x = {xi}:  f = {yi},  f'' = {f2i}  →  {kind}")
print("  Expected: f(-1)=10 local maximum, f(3)=-22 local minimum.")

f_num  = lambdify(x, f,  'numpy')
f1_num = lambdify(x, f1, 'numpy')
f2_num = lambdify(x, f2, 'numpy')

xs = np.linspace(-4, 6, 800)

# Combined plot of f, f', f''
plt.figure(figsize=(7.5, 5))
plt.plot(xs, f_num(xs),  'b-',  lw=2,   label=r"$f(x)=x^3-3x^2-9x+5$")
plt.plot(xs, f1_num(xs), 'g--', lw=1.8, label=r"$f'(x)=3x^2-6x-9$")
plt.plot(xs, f2_num(xs), 'r:',  lw=1.8, label=r"$f''(x)=6x-6$")
plt.axhline(0, color='k', lw=0.6)
for xi in crits:
    plt.scatter([float(xi)], [float(f.subs(x, xi))], color='darkred', s=70, zorder=5)
    plt.annotate(f"({xi}, {f.subs(x, xi)})", (float(xi), float(f.subs(x, xi))),
                 textcoords="offset points", xytext=(8, 8), fontsize=9)
plt.grid(alpha=0.3); plt.legend(fontsize=9); plt.xlabel('x')
plt.title("Ch. 11 — f, f′ and f″ on one plot")
plt.tight_layout()

# ── B. Automatic sign table of f' (np.sign + axvspan) ─────
print("\n── B. Sign table of f' (np.sign on a dense grid) ──")

xg = np.linspace(-4, 6, 2001)
s1_all = np.sign(f1_num(xg))

# We ignore the points where f'=0 (there the sign is undefined) and
# look only at successive NON-zero signs.
nz = np.nonzero(s1_all)[0]
s1 = s1_all[nz]
xnz = xg[nz]
changes = np.where(np.diff(s1) != 0)[0]
print(f"  Sign changes of f' between x = "
      f"{np.round(xnz[changes], 3)} and {np.round(xnz[changes + 1], 3)}"
      f"   (expected ~ -1 and 3)")
for i in changes:
    before, after = s1[i], s1[i + 1]
    if before > 0 > after:
        kind = "local MAXIMUM (+ → -)"
    elif before < 0 < after:
        kind = "local MINIMUM (- → +)"
    else:
        kind = "no change"
    print(f"    on the interval [{xnz[i]:7.3f}, {xnz[i+1]:7.3f}]: "
          f"{before:+.0f} → {after:+.0f}  ⇒  {kind}")

# Intervals of monotonicity from the critical points
bounds = [-np.inf] + [float(c) for c in crits] + [np.inf]
mono = []
print("\n  Monotonicity table (one test value per interval):")
for a, b in zip(bounds[:-1], bounds[1:]):
    # test value inside the interval
    if np.isinf(a):
        t = b - 1.0
    elif np.isinf(b):
        t = a + 1.0
    else:
        t = 0.5*(a + b)
    v = float(f1_num(t))
    lab = "INCREASING" if v > 0 else ("DECREASING" if v < 0 else "-")
    mono.append((a, b, v > 0))
    astr = "-∞" if np.isinf(a) else f"{a:g}"
    bstr = "+∞" if np.isinf(b) else f"{b:g}"
    print(f"    ({astr}, {bstr}):  x={t:6.2f} → f'={v:9.3f}  "
          f"{'(+)' if v > 0 else '(-)'}  {lab}")

# Plot of f with the increasing/decreasing intervals shaded
fig, ax = plt.subplots(figsize=(8, 5))
ax.plot(xs, f_num(xs), 'b-', lw=2.2, label=r"$f(x)=x^3-3x^2-9x+5$")
for a, b, inc in mono:
    a_p = max(a, xs[0]); b_p = min(b, xs[-1])
    ax.axvspan(a_p, b_p, color=('#bfe6bf' if inc else '#f6c6c6'), alpha=0.55)
ax.axhline(0, color='k', lw=0.6)
for xi in crits:
    ax.scatter([float(xi)], [float(f.subs(x, xi))], color='darkred', s=70, zorder=5)
ax.set_xlim(xs[0], xs[-1])
ax.grid(alpha=0.3); ax.set_xlabel('x')
ax.set_title("Monotonicity: green = increasing (f′>0), red = decreasing (f′<0)")
ax.legend(fontsize=9)
plt.tight_layout()

# ── C. Inflection points and convexity / concavity ────────
print("\n── C. Inflection points — convex / concave regions ──")

infl = sorted(solve(f2, x))
print(f"  Inflection points (f''=0): x = {infl}   (expected [1])")
for xi in infl:
    print(f"    x = {xi}:  f = {f.subs(x, xi)}   (expected f(1) = -6)")

# Verification of the sign change of f'' at each inflection point
eps = 0.1
for xi in infl:
    left  = float(f2_num(float(xi) - eps))
    right = float(f2_num(float(xi) + eps))
    print(f"    f''({float(xi)-eps:g}) = {left:+.3f},  "
          f"f''({float(xi)+eps:g}) = {right:+.3f}  →  "
          f"sign change: {left*right < 0}")

# Intervals of convexity
cb = [-np.inf] + [float(i) for i in infl] + [np.inf]
conv = []
print("\n  Convexity table:")
for a, b in zip(cb[:-1], cb[1:]):
    if np.isinf(a):
        t = b - 1.0
    elif np.isinf(b):
        t = a + 1.0
    else:
        t = 0.5*(a + b)
    v = float(f2_num(t))
    lab = "CONVEX (concave up)" if v > 0 else ("CONCAVE (concave down)" if v < 0 else "-")
    conv.append((a, b, v > 0))
    astr = "-∞" if np.isinf(a) else f"{a:g}"
    bstr = "+∞" if np.isinf(b) else f"{b:g}"
    print(f"    ({astr}, {bstr}):  x={t:6.2f} → f''={v:9.3f}  "
          f"{'(+)' if v > 0 else '(-)'}  {lab}")

fig, ax = plt.subplots(figsize=(8, 5))
ax.plot(xs, f_num(xs), 'b-', lw=2.2, label=r"$f(x)$")
ax.plot(xs, f2_num(xs), 'r:', lw=1.5, label=r"$f''(x)$")
for a, b, cx in conv:
    a_p = max(a, xs[0]); b_p = min(b, xs[-1])
    ax.axvspan(a_p, b_p, color=('#c9d8f2' if cx else '#f2e3c0'), alpha=0.65)
ax.axhline(0, color='k', lw=0.6)
for xi in infl:
    ax.scatter([float(xi)], [float(f.subs(x, xi))], color='purple', s=80, zorder=5)
    ax.annotate(f"inflection ({xi}, {f.subs(x, xi)})",
                (float(xi), float(f.subs(x, xi))),
                textcoords="offset points", xytext=(10, -18), fontsize=9)
ax.set_xlim(xs[0], xs[-1])
ax.grid(alpha=0.3); ax.set_xlabel('x')
ax.set_title("Convexity: blue = convex (f″>0), ochre = concave (f″<0)")
ax.legend(fontsize=9)
plt.tight_layout()

# ── D. Mean Value Theorem ─────────────────────────────────
print("\n── D. Mean Value Theorem ──")


def mvt(expr, a, b, name):
    """Finds c in (a,b) with f'(c) = (f(b)-f(a))/(b-a) and returns it."""
    fa, fb = expr.subs(x, a), expr.subs(x, b)
    slope = simplify((fb - fa)/(b - a))
    d = diff(expr, x)
    sols = [s for s in solve(d - slope, x) if s.is_real and a < s < b]
    print(f"\n  {name} on [{a}, {b}]")
    print(f"    f({a}) = {fa},  f({b}) = {fb}")
    print(f"    slope of the chord = {slope}  ( = {float(slope):.6f} )")
    print(f"    f'(x) = {d}")
    print(f"    solutions of f'(c) = slope in ({a},{b}): c = {sols}")
    return fa, fb, slope, sols


# (i) f(x) = x^2 - x + 1 on [1,4]  -> c = 5/2
g1 = x**2 - x + 1
a1, b1 = 1, 4
fa1, fb1, m1, cs1 = mvt(g1, a1, b1, "f(x) = x² - x + 1")
c1 = cs1[0]
gc1 = g1.subs(x, c1)
chord1   = fa1 + m1*(x - a1)
tangent1 = gc1 + m1*(x - c1)
print(f"    c = {c1}  (expected 5/2),  f(c) = {gc1}  (expected 19/4)")
print(f"    chord:   y = {chord1.expand()}   (expected 4x - 3)")
print(f"    tangent: y = {tangent1.expand()}   (expected 4x - 21/4)")
print(f"    slopes: chord {diff(chord1, x)}, tangent {diff(tangent1, x)} "
      f"→ parallel: {simplify(diff(chord1, x) - diff(tangent1, x)) == 0}")

g1n = lambdify(x, g1, 'numpy')
ch1n = lambdify(x, chord1, 'numpy')
tg1n = lambdify(x, tangent1, 'numpy')
xx1 = np.linspace(0.5, 4.5, 400)

# (ii) g(x) = sqrt(x) on [0,4]  -> c = 1
g2 = sqrt(x)
a2, b2 = 0, 4
fa2, fb2, m2, cs2 = mvt(g2, a2, b2, "g(x) = √x")
c2 = cs2[0]
gc2 = g2.subs(x, c2)
chord2   = fa2 + m2*(x - a2)
tangent2 = gc2 + m2*(x - c2)
print(f"    c = {c2}  (expected 1),  g(c) = {gc2}  (expected 1)")
print(f"    chord:   y = {chord2.expand()}   (expected x/2)")
print(f"    tangent: y = {tangent2.expand()}   (expected x/2 + 1/2)")
print(f"    slopes: chord {diff(chord2, x)}, tangent {diff(tangent2, x)} "
      f"→ parallel: {simplify(diff(chord2, x) - diff(tangent2, x)) == 0}")

# Comment on the differentiability hypothesis at the ENDPOINTS
dg2 = diff(g2, x)
lim0 = limit(dg2, x, 0, '+')
print(f"\n    COMMENT: g'(x) = {dg2}, and lim_(x→0+) g'(x) = {lim0}.")
print("    √x is NOT differentiable at the endpoint x=0 (vertical tangent).")
print("    The MVT requires continuity on the CLOSED [a,b] and differentiability")
print("    only on the OPEN (a,b) — so the hypotheses DO HOLD here as well,")
print("    which is why c = 1 was found in (0,4).")

g2n = lambdify(x, g2, 'numpy')
ch2n = lambdify(x, chord2, 'numpy')
tg2n = lambdify(x, tangent2, 'numpy')
xx2 = np.linspace(0, 4.5, 400)

fig, axes = plt.subplots(1, 2, figsize=(12, 4.6))

ax = axes[0]
ax.plot(xx1, g1n(xx1), 'b-', lw=2.2, label=r"$f(x)=x^2-x+1$")
ax.plot(xx1, ch1n(xx1), 'g--', lw=1.8, label="chord A(1,1)–B(4,13)")
ax.plot(xx1, tg1n(xx1), 'r-.', lw=1.8, label=f"tangent at c={c1}")
ax.scatter([a1, b1], [float(fa1), float(fb1)], color='green', s=60, zorder=5)
ax.scatter([float(c1)], [float(gc1)], color='red', s=80, zorder=5)
ax.axvline(float(c1), color='0.6', lw=0.8, ls=':')
ax.grid(alpha=0.3); ax.legend(fontsize=8); ax.set_xlabel('x')
ax.set_title(f"MVT on [1,4]:  c = {c1}")

ax = axes[1]
ax.plot(xx2, g2n(xx2), 'b-', lw=2.2, label=r"$g(x)=\sqrt{x}$")
ax.plot(xx2, ch2n(xx2), 'g--', lw=1.8, label="chord A(0,0)–B(4,2)")
ax.plot(xx2, tg2n(xx2), 'r-.', lw=1.8, label=f"tangent at c={c2}")
ax.scatter([a2, b2], [float(fa2), float(fb2)], color='green', s=60, zorder=5)
ax.scatter([float(c2)], [float(gc2)], color='red', s=80, zorder=5)
ax.axvline(float(c2), color='0.6', lw=0.8, ls=':')
ax.set_ylim(-0.3, 3.2)
ax.grid(alpha=0.3); ax.legend(fontsize=8); ax.set_xlabel('x')
ax.set_title(f"MVT for √x on [0,4]:  c = {c2}\n(not differentiable at the endpoint x=0)")

plt.tight_layout()
plt.show()

print("\nChapter 11 completed.")
