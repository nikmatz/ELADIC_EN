# ============================================================
# python_deriv.py
# Chapter 8 — The Derivative
# Matzakos, N. (2026). Elements of Linear Algebra, Differential & Integral Calculus. NewTech Publications.
# ============================================================
#
# LIBRARIES:
#   sympy      → symbolic differentiation (diff, simplify)
#   numpy      → numerical differentiation (gradient, central diff)
#   matplotlib → graphs (f, f', f'', tangent line)
#
# BASIC COMMANDS:
#   sympy.diff(f, x)      → f'(x)
#   sympy.diff(f, x, n)   → f⁽ⁿ⁾(x)
#   f_expr.subs(x, a)     → f(a)
#   sympy.lambdify(x, f)  → conversion to a numerical function
#   np.gradient(y, dx)    → numerical derivative
# ============================================================

import numpy as np
import matplotlib.pyplot as plt
from sympy import (symbols, diff, sin, cos, tan, exp, log, sqrt,
                   simplify, trigsimp, expand, limit, lambdify,
                   pprint, Rational, pi, oo)

x, h = symbols('x h')

print("=" * 55)
print(" Chapter 8: The Derivative — Python")
print("=" * 55)

# ── A. Basic Derivatives ─────────────────────────────────
print("\n── A. Basic Derivatives ──")

funcs = [
    ("3x⁴ - 5x² + 2x - 7",  3*x**4 - 5*x**2 + 2*x - 7),
    ("sin(x)",               sin(x)),
    ("cos(x)",               cos(x)),
    ("tan(x)",               tan(x)),
    ("e^x",                  exp(x)),
    ("e^(3x)",               exp(3*x)),
    ("ln(x)",                log(x)),
    ("ln(x²+1)",             log(x**2+1)),
    ("x^x  (log. diff.)",   x**x),
]

for label, f in funcs:
    fp = simplify(diff(f, x))
    print(f"  d/dx[{label}] = {fp}")

# ── B. Differentiation Rules ─────────────────────────────
print("\n── B. Differentiation Rules ──")

f_prod = x**2 * sin(x)
f_quot = (x**3 + 1) / (x**2 - 1)
f_chain = sin(x**2 + 1)
f_comp  = exp(sin(x)**2)

print(f"  Product rule:  (x²·sin x)' = {expand(diff(f_prod, x))}")
print(f"  Quotient rule: [(x³+1)/(x²-1)]' = {simplify(diff(f_quot, x))}")
print(f"  Chain rule:    [sin(x²+1)]' = {diff(f_chain, x)}")
print(f"  Composite:     [e^(sin²x)]' = {simplify(diff(f_comp, x))}")

# ── C. Higher-Order Derivatives ──────────────────────────
print("\n── C. Higher-Order Derivatives ──")

f_e = exp(x) * cos(x)
print("f(x) = eˣcos(x)")
for n in range(1, 5):
    dn = trigsimp(diff(f_e, x, n))
    print(f"  f{'⁽'+str(n)+'⁾'} = {dn}")
print(f"  f⁽⁴⁾ + 4f = {trigsimp(diff(f_e,x,4) + 4*f_e)}  (= 0 ✓)")

# ── D. The Derivative from the Definition ────────────────
print("\n── D. The Derivative from the Definition ──")

for f_def, label in [(x**2, "x²"), (sqrt(x), "√x"), (sin(x), "sin(x)")]:
    fp_def = limit((f_def.subs(x, x+h) - f_def) / h, h, 0)
    print(f"  d/dx[{label}] = {simplify(fp_def)}")

# ── E. Tangent & Normal Line ────────────────────────────
print("\n── E. The Tangent Line ──")

f_tan_sym = x**3 - 2*x + 1
x0 = 1
y0 = f_tan_sym.subs(x, x0)
m  = diff(f_tan_sym, x).subs(x, x0)
print(f"  f(x) = x³-2x+1,  x₀={x0}")
print(f"  f(x₀)={y0},  f'(x₀)={m}")
print(f"  Tangent: y = {m}(x-{x0}) + {y0}  =  {m}x + {y0-m*x0}")
print(f"  Normal:  y = {-1/m}(x-{x0}) + {y0}")

# ── F. Numerical Differentiation (NumPy) ─────────────────
print("\n── F. Numerical Differentiation (NumPy) ──")

t = np.linspace(0.01, 2*np.pi, 1000)
dt = t[1] - t[0]
f_num   = np.sin(t)
fp_num  = np.gradient(f_num, dt)         # numerical derivative
fp_exact = np.cos(t)                     # exact

error = np.max(np.abs(fp_num - fp_exact))
print(f"  Maximum error of the numerical derivative of sin(x): {error:.2e}  ✓")

# ── G. Graphs ────────────────────────────────────────────
print("\n── G. Graphs ──")

# Conversion sympy → numpy
f_np  = lambdify(x, f_tan_sym,          'numpy')
fp_np = lambdify(x, diff(f_tan_sym, x), 'numpy')
fpp_np= lambdify(x, diff(f_tan_sym, x, 2), 'numpy')

fig, axes = plt.subplots(1, 3, figsize=(14, 4.5))
fig.suptitle("The Derivative — Graphs", fontsize=13, fontweight='bold')

t2 = np.linspace(-2, 2.5, 500)

# --- f, f', f'' ---
ax1 = axes[0]
ax1.plot(t2, f_np(t2),   'royalblue', lw=2.5, label='$f(x)=x^3-2x+1$')
ax1.plot(t2, fp_np(t2),  'tomato',    lw=2,   label="$f'(x)=3x^2-2$")
ax1.plot(t2, fpp_np(t2), 'forestgreen', lw=2, label="$f''(x)=6x$")
ax1.axhline(0,color='k',lw=0.5)
ax1.set_title("$f$, $f'$, $f''$", fontsize=10)
ax1.legend(fontsize=8); ax1.grid(True,alpha=0.3)
ax1.set_xlim(-2,2.5); ax1.set_ylim(-6,8)

# --- Tangent line ---
ax2 = axes[1]
tang = float(m)*(t2 - x0) + float(y0)
ax2.plot(t2, f_np(t2), 'royalblue', lw=2.5, label='$f(x)$')
ax2.plot(t2, tang,     'tomato', lw=1.8, ls='--', label=f'Tangent at x₀={x0}')
ax2.plot(x0, float(y0), 'ko', ms=7, zorder=5)
ax2.set_title("Tangent line at $x_0=1$", fontsize=10)
ax2.legend(fontsize=8); ax2.grid(True,alpha=0.3)
ax2.set_xlim(-2,2.5); ax2.set_ylim(-4,6)

# --- Numerical vs Exact derivative ---
ax3 = axes[2]
ax3.plot(t, fp_exact, 'royalblue', lw=2.5, label='cos(x) (exact)')
ax3.plot(t, fp_num,   'tomato', lw=1.5, ls='--', label="np.gradient (numerical)")
ax3.set_title("Numerical vs Exact derivative\n$f(x)=\\sin(x)$", fontsize=10)
ax3.legend(fontsize=8); ax3.grid(True,alpha=0.3)

plt.tight_layout()
plt.savefig("derivatives.png", dpi=120, bbox_inches='tight')
print("The figure has been saved: derivatives.png")
plt.show()
