# ============================================================
# python_paragogos.py
# Chapter 10 — The Derivative: SymPy, NumPy, Graphics
# Matzakos, N. (2026). Elements of Linear Algebra, Differential & Integral Calculus. NewTech Publications.
# ============================================================
#
# LIBRARIES:
#   sympy       → symbolic differentiation
#   numpy       → numerical derivative from sampled values
#   matplotlib  → plots of f, f', f'' and of the tangent line
#
# BASIC COMMANDS:
#   sympy.diff(f, x)        → f'(x)
#   sympy.diff(f, x, n)     → nth derivative
#   f.subs(x, a)            → value at a
#   sympy.lambdify(x, f)    → symbolic → numerical
#   np.gradient(y, x)       → numerical derivative (central differences)
# ============================================================

import numpy as np
import matplotlib.pyplot as plt
from sympy import (symbols, diff, simplify, factor, expand, lambdify,
                   sin, cos, exp, log, sqrt, limit)

x, h = symbols('x h')

print("=" * 58)
print(" Chapter 10: The Derivative of a Function — Python")
print("=" * 58)

# ── A. Derivatives with sympy.diff — comparison with Maxima ─
print("\n── A. Basic rules (sympy.diff) ──")

# The same functions as in the Maxima activity.
casesA = [
    ("3x^4-5x^2+2x-7", 3*x**4 - 5*x**2 + 2*x - 7, 12*x**3 - 10*x + 2),
    ("sin(x)",          sin(x),                    cos(x)),
    ("e^(3x)",          exp(3*x),                  3*exp(3*x)),
    ("ln(x^2+1)",       log(x**2 + 1),             2*x/(x**2 + 1)),
]
for name, f_, expected in casesA:
    d = simplify(diff(f_, x))
    same = simplify(d - expected) == 0
    print(f"  ({name})' = {d}")
    print(f"      expected: {expected}   identical: {same}")

# ── B. Product — Quotient — Chain ─────────────────────────
print("\n── B. Product, quotient, chain ──")

casesB = [
    ("x^2 sin(x)",        x**2*sin(x),             2*x*sin(x) + x**2*cos(x)),
    ("(x^3+1)/(x^2-1)",   (x**3 + 1)/(x**2 - 1),   x*(x - 2)/(x - 1)**2),
    ("sin(x^2+1)",        sin(x**2 + 1),           2*x*cos(x**2 + 1)),
]
for name, f_, expected in casesB:
    d = factor(simplify(diff(f_, x)))
    same = simplify(diff(f_, x) - expected) == 0
    print(f"  ({name})' = {d}")
    print(f"      expected: {expected}   identical: {same}")

# ── C. Higher order: f(x)=e^x cos(x), f^(4) = -4f ─────────
print("\n── C. Higher order: f(x)=e^x·cos(x) ──")

fC = exp(x)*cos(x)
for n in range(1, 5):
    print(f"  f^({n})(x) = {expand(diff(fC, x, n))}")
print(f"  f^(4) + 4f = {simplify(diff(fC, x, 4) + 4*fC)}   "
      f"→ f^(4) = -4f holds: {simplify(diff(fC, x, 4) + 4*fC) == 0}")

# ── D. f(x)=x^3-2x+1: lambdify and plot of f, f', f'' ─────
print("\n── D. f(x)=x^3-2x+1 on [-2, 2.5] (lambdify) ──")

fD  = x**3 - 2*x + 1
f1D = diff(fD, x)
f2D = diff(fD, x, 2)
print(f"  f(x)   = {fD}")
print(f"  f'(x)  = {f1D}      (expected 3x^2-2)")
print(f"  f''(x) = {f2D}      (expected 6x)")

f_num  = lambdify(x, fD,  'numpy')
f1_num = lambdify(x, f1D, 'numpy')
f2_num = lambdify(x, f2D, 'numpy')

xs = np.linspace(-2, 2.5, 400)
plt.figure(figsize=(7, 4.5))
plt.plot(xs, f_num(xs),  'b-',  lw=2,   label=r"$f(x)=x^3-2x+1$")
plt.plot(xs, f1_num(xs), 'g--', lw=1.8, label=r"$f'(x)=3x^2-2$")
plt.plot(xs, f2_num(xs), 'r:',  lw=1.8, label=r"$f''(x)=6x$")
plt.axhline(0, color='k', lw=0.6)
plt.grid(alpha=0.3); plt.legend(); plt.xlabel('x')
plt.title("Ch. 10 — f, f' and f'' on [-2, 2.5]")
plt.tight_layout()

# Check: lambdify and sympy give the same value.
print(f"  Check of lambdify at x=2: f'(2) = {f1_num(2.0)} "
      f"(sympy: {f1D.subs(x, 2)})")

# ── E. Numerical derivative with np.gradient ──────────────
print("\n── E. Numerical derivative: np.gradient for sin(x) ──")

xg = np.linspace(0, 2*np.pi, 400)
yg = np.sin(xg)
dyg = np.gradient(yg, xg)               # central differences
err = np.max(np.abs(dyg - np.cos(xg)))
print(f"  max |np.gradient(sin) - cos| = {err:.3e}")

# Forward difference (the definition, with a finite h):
for hh in (1e-1, 1e-3, 1e-5):
    fd = (np.sin(1.0 + hh) - np.sin(1.0))/hh
    print(f"  h={hh:<8g} (f(1+h)-f(1))/h = {fd:.8f}   "
          f"error vs cos(1)={abs(fd - np.cos(1.0)):.2e}")
print(f"  cos(1) = {np.cos(1.0):.8f}")

# Second derivative: np.gradient applied twice
d2g = np.gradient(dyg, xg)
print(f"  max |second derivative + sin| (interior points) = "
      f"{np.max(np.abs(d2g + np.sin(xg))[5:-5]):.3e}")

plt.figure(figsize=(7, 4))
plt.plot(xg, dyg, 'b-', lw=2.5, label=r"np.gradient$(\sin x)$")
plt.plot(xg, np.cos(xg), 'r--', lw=1.5, label=r"$\cos x$ (exact)")
plt.axhline(0, color='k', lw=0.6)
plt.grid(alpha=0.3); plt.legend(); plt.xlabel('x')
plt.title("Numerical vs analytic derivative of sin")
plt.tight_layout()

# ── F. Tangent line at x0=1 — geometric interpretation ────
print("\n── F. Tangent to f(x)=x^3-2x+1 at x0=1 ──")

x0 = 1
y0 = fD.subs(x, x0)
m  = f1D.subs(x, x0)
tangent = expand(y0 + m*(x - x0))
print(f"  f(1) = {y0},  f'(1) = {m}")
print(f"  Tangent: y = {tangent}   (expected y = x - 1)")
print(f"  Identical with x-1: {simplify(tangent - (x - 1)) == 0}")

t_num = lambdify(x, tangent, 'numpy')
xs2 = np.linspace(-2, 2.5, 400)

plt.figure(figsize=(7, 4.5))
plt.plot(xs2, f_num(xs2), 'b-', lw=2, label=r"$f(x)=x^3-2x+1$")
plt.plot(xs2, t_num(xs2), 'r--', lw=1.8, label=f"tangent: y = {tangent}")
plt.scatter([float(x0)], [float(y0)], color='red', s=70, zorder=5,
            label=f"point of tangency ({x0}, {y0})")
# Secants that "approach" the tangent as h→0:
for hh, col in [(1.0, '0.75'), (0.5, '0.55'), (0.25, '0.35')]:
    xa, xb = 1.0, 1.0 + hh
    ya, yb = float(f_num(xa)), float(f_num(xb))
    ms = (yb - ya)/hh
    plt.plot(xs2, ya + ms*(xs2 - xa), color=col, lw=1,
             label=f"secant h={hh} (slope {ms:.2f})")
plt.axhline(0, color='k', lw=0.6)
plt.ylim(-4, 8); plt.grid(alpha=0.3); plt.legend(fontsize=8)
plt.xlabel('x'); plt.title("The tangent as a limit of secants (x₀=1)")
plt.tight_layout()

print("  Slopes of the secants (h→0) — they converge to f'(1)=1:")
for hh in (1.0, 0.5, 0.25, 0.1, 0.01):
    ms = (float(f_num(1.0 + hh)) - float(f_num(1.0)))/hh
    print(f"    h={hh:<6g} slope = {ms:.6f}")

# ── G. The derivative from the definition (symbolic limit) ─
print("\n── G. The definition: lim_{h→0} (f(x+h)-f(x))/h ──")
print(f"  x^2     → {limit(((x + h)**2 - x**2)/h, h, 0)}      "
      f"(diff: {diff(x**2, x)})")
print(f"  sqrt(x) → {limit((sqrt(x + h) - sqrt(x))/h, h, 0)}   "
      f"(diff: {diff(sqrt(x), x)})")

# ── H. Optional: logarithmic differentiation (x^x)' ───────
print("\n── H. Optional: logarithmic differentiation (x^x)' ──")

xp = symbols('x', positive=True)
fH = xp**xp
dH = simplify(diff(fH, xp))
expected_H = xp**xp*(log(xp) + 1)
print(f"  (x^x)' = {dH}")
print(f"  expected: x^x·(ln x + 1) = {expand(expected_H)}")
print(f"  Difference: {simplify(dH - expected_H)}  "
      f"→ identical: {simplify(dH - expected_H) == 0}")
# Numerical check at x=2:  (x^x)'(2) = 4(ln2+1)
val_sym = float(dH.subs(xp, 2))
val_num = 2.0**2.0*(np.log(2.0) + 1.0)
print(f"  At x=2: symbolically {val_sym:.10f}, formula {val_num:.10f}, "
      f"difference {abs(val_sym - val_num):.2e}")

plt.show()
print("\nChapter 10 completed.")
