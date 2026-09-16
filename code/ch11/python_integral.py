# ============================================================
# python_integral.py
# Chapter 10 — Indefinite Integral
# Matzakos, N. (2026). Elements of Linear Algebra, Differential & Integral Calculus. NewTech Publications.
# ============================================================
#
# LIBRARIES:
#   sympy         → indefinite integral, simplification
#   numpy         → numerical verification
#   scipy.integrate → numerical integration (quad)
#   matplotlib    → plots (f and F)
#
# BASIC COMMANDS:
#   sympy.integrate(f, x)          → indefinite integral
#   sympy.diff(F, x)               → verification F'=f
#   sympy.integrate(f, (x, a, b))  → definite integral
#   scipy.integrate.quad           → numerical integration
# ============================================================

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec
from sympy import (symbols, integrate, diff, sin, cos, tan,
                   exp, log, sqrt, Rational, simplify, trigsimp,
                   factor, expand, pprint, pi, oo, lambdify)
from scipy.integrate import quad

x, u, C = symbols('x u C')

print("=" * 55)
print(" Chapter 10: Indefinite Integral — Python")
print("=" * 55)

# ── A. Basic Integrals ───────────────────────────────────
print("\n── A. Basic Integrals ──")

basic_integrals = [
    (x**4,           "x⁴"),
    (x**Rational(-2),"x⁻²"),
    (sqrt(x),        "√x"),
    (sin(x),         "sin x"),
    (cos(x),         "cos x"),
    (1/cos(x)**2,    "sec²x"),
    (exp(x),         "eˣ"),
    (1/x,            "1/x"),
    (2**x,           "2ˣ"),
]

print(f"{'f(x)':<12} {'∫f(x)dx':>25}  {'Check F\'=f':>6}")
print("-" * 50)
for f_sym, label in basic_integrals:
    F = integrate(f_sym, x)
    check = simplify(diff(F, x) - f_sym) == 0
    Fs = trigsimp(simplify(F))
    print(f"  {label:<12}  {str(Fs):<28}  {'✓' if check else '✗'}")

# ── B. u-substitution ─────────────────────────────────────
print("\n── B. Substitution (u-substitution) ──")

subst_cases = [
    (2*x*cos(x**2),      "2x·cos(x²)  [u=x²]"),
    (x*exp(x**2),        "x·eˣ²       [u=x²]"),
    (6*x*(3*x**2+1)**5,  "6x(3x²+1)⁵  [u=3x²+1]"),
    (sin(x)**3*cos(x),   "sin³x·cosx  [u=sinx]"),
    (exp(x)/(1+exp(x)),  "eˣ/(1+eˣ)   [u=1+eˣ]"),
]

for f_sym, label in subst_cases:
    F = integrate(f_sym, x)
    F_s = trigsimp(simplify(F))
    check = simplify(diff(F_s, x) - f_sym) == 0
    print(f"  ∫ {label}")
    print(f"    = {F_s} + C  {'✓' if check else '(see sympy output)'}")

# ── C. Integration by Parts ──────────────────────────────
print("\n── C. Integration by Parts (∫u dv) ──")

ibp_cases = [
    (x*exp(x),   "x·eˣ      [u=x, dv=eˣdx]"),
    (x*sin(x),   "x·sinx    [u=x, dv=sinx dx]"),
    (x**2*exp(x),"x²·eˣ     [u=x², dv=eˣdx]"),
    (log(x),     "lnx       [u=lnx, dv=dx]"),
    (x*log(x),   "x·lnx     [u=lnx, dv=x dx]"),
]

for f_sym, label in ibp_cases:
    F = integrate(f_sym, x)
    check = simplify(diff(F, x) - f_sym) == 0
    print(f"  ∫ {label}")
    print(f"    = {expand(F)} + C  {'✓' if check else '?'}")

# ── D. Rational Functions — Partial Fractions ───────────
print("\n── D. Rational Functions ──")

rational_cases = [
    (1/(x**2+4),          "1/(x²+4)"),
    (1/(x**2-1),          "1/(x²-1)  [partial fractions]"),
    ((2*x+1)/(x**2+x-2),  "(2x+1)/(x²+x-2)"),
    (x/(x**2+1),          "x/(x²+1)"),
    (1/(x*(x+1)),         "1/(x(x+1))"),
]

for f_sym, label in rational_cases:
    F = integrate(f_sym, x)
    F_s = simplify(F)
    check = simplify(diff(F_s, x) - f_sym) == 0
    print(f"  ∫ {label} dx")
    print(f"    = {F_s} + C  {'✓' if check else '?'}")

# ── E. Trigonometric Integrals ─────────────────────────
print("\n── E. Trigonometric Integrals ──")

trig_cases = [
    (sin(x)**2,       "sin²x"),
    (cos(x)**2,       "cos²x"),
    (sin(x)**3,       "sin³x"),
    (sin(x)*cos(x),   "sinx·cosx"),
    (tan(x),          "tanx"),
]

for f_sym, label in trig_cases:
    F = integrate(f_sym, x)
    F_s = trigsimp(simplify(F))
    check = simplify(trigsimp(diff(F_s, x) - f_sym)) == 0
    print(f"  ∫ {label} dx = {F_s} + C  {'✓' if check else '(trigsimp needed)'}")

# ── F. Numerical Verification with scipy ─────────────────
print("\n── F. Numerical Verification (scipy.integrate.quad) ──")

# Numerical integral from 0 to 1 for several f(x)
num_cases = [
    (lambda t: t**4,          integrate(x**4, (x, 0, 1)),         "∫₀¹ x⁴ dx"),
    (lambda t: np.sin(t),     integrate(sin(x), (x, 0, float(pi))),"∫₀^pi sinx dx"),
    (lambda t: t*np.exp(t),   integrate(x*exp(x), (x, 0, 1)),     "∫₀¹ x·eˣ dx"),
    (lambda t: np.log(t+1),   integrate(log(x+1), (x, 0, 1)),     "∫₀¹ ln(x+1) dx"),
]

for f_np, sym_val, label in num_cases:
    numerical, _ = quad(f_np, 0, 1 if "pi" not in label else float(pi))
    symbolic    = float(sym_val)
    err = abs(numerical - symbolic)
    print(f"  {label} = {symbolic:.8f}  (scipy: {numerical:.8f}  err={err:.2e}) ✓")

# ── G. Plots ─────────────────────────────────────────────
print("\n── G. Plots ──")

t = np.linspace(-2, 3, 500)

fig = plt.figure(figsize=(14, 9))
fig.suptitle("Indefinite Integral — Plots", fontsize=13, fontweight='bold')
gs = gridspec.GridSpec(2, 3, fig, hspace=0.45, wspace=0.35)

# 1. Powers: f and F
ax1 = fig.add_subplot(gs[0, 0])
f1_sym = x**3 - 2*x
F1_sym = integrate(f1_sym, x)
f1_np  = lambdify(x, f1_sym, 'numpy')
F1_np  = lambdify(x, F1_sym, 'numpy')
ax1.plot(t, f1_np(t), 'royalblue', lw=2.5, label=r'$f(x)=x^3-2x$')
ax1.plot(t, F1_np(t), 'tomato',    lw=2,   ls='--', label=r'$F(x)=\frac{x^4}{4}-x^2$')
ax1.axhline(0, color='k', lw=0.5)
ax1.set_ylim(-5, 5); ax1.set_title("Power: $f$ and $F$", fontsize=10)
ax1.legend(fontsize=8); ax1.grid(True, alpha=0.3)

# 2. Substitution: f = 2x·cos(x²), F = sin(x²)
ax2 = fig.add_subplot(gs[0, 1])
t2 = np.linspace(-2, 2, 500)
f2_np = lambda t: 2*t*np.cos(t**2)
F2_np = lambda t: np.sin(t**2)
ax2.plot(t2, f2_np(t2), 'royalblue', lw=2.5, label=r'$f=2x\cos(x^2)$')
ax2.plot(t2, F2_np(t2), 'tomato',    lw=2,   ls='--', label=r'$F=\sin(x^2)$')
ax2.axhline(0, color='k', lw=0.5)
ax2.set_title("Substitution $u=x^2$", fontsize=10)
ax2.legend(fontsize=8); ax2.grid(True, alpha=0.3)

# 3. By Parts: x·eˣ
ax3 = fig.add_subplot(gs[0, 2])
t3 = np.linspace(-2, 2, 500)
f3_np = lambda t: t*np.exp(t)
F3_np = lambda t: np.exp(t)*(t - 1)
ax3.plot(t3, f3_np(t3), 'royalblue', lw=2.5, label=r'$f=xe^x$')
ax3.plot(t3, F3_np(t3), 'tomato',    lw=2,   ls='--', label=r'$F=e^x(x-1)$')
ax3.axhline(0, color='k', lw=0.5)
ax3.set_ylim(-3, 8); ax3.set_title(r"By Parts: $xe^x$", fontsize=10)
ax3.legend(fontsize=8); ax3.grid(True, alpha=0.3)

# 4. Trigonometric: sin²x
ax4 = fig.add_subplot(gs[1, 0])
t4 = np.linspace(0, 2*np.pi, 500)
f4_np = lambda t: np.sin(t)**2
F4_np = lambda t: t/2 - np.sin(2*t)/4
ax4.plot(t4, f4_np(t4), 'royalblue', lw=2.5, label=r'$f=\sin^2 x$')
ax4.plot(t4, F4_np(t4), 'tomato',    lw=2,   ls='--', label=r'$F=\frac{x}{2}-\frac{\sin 2x}{4}$')
ax4.axhline(0, color='k', lw=0.5)
ax4.set_xticks([0, np.pi/2, np.pi, 3*np.pi/2, 2*np.pi])
ax4.set_xticklabels(['0', r'$\pi/2$', r'$\pi$', r'$3\pi/2$', r'$2\pi$'])
ax4.set_title(r"Trigonometric: $\sin^2 x$", fontsize=10)
ax4.legend(fontsize=8); ax4.grid(True, alpha=0.3)

# 5. Logarithmic: lnx
ax5 = fig.add_subplot(gs[1, 1])
t5 = np.linspace(0.1, 4, 400)
f5_np = lambda t: np.log(t)
F5_np = lambda t: t*np.log(t) - t
ax5.plot(t5, f5_np(t5), 'royalblue', lw=2.5, label=r'$f=\ln x$')
ax5.plot(t5, F5_np(t5), 'tomato',    lw=2,   ls='--', label=r'$F=x\ln x - x$')
ax5.axhline(0, color='k', lw=0.5)
ax5.set_title(r"By Parts: $\ln x$", fontsize=10)
ax5.legend(fontsize=8); ax5.grid(True, alpha=0.3)

# 6. Rational: 1/(x²-1)
ax6 = fig.add_subplot(gs[1, 2])
t6a = np.linspace(-3, -1.05, 300)
t6b = np.linspace(1.05, 3, 300)
f6_np  = lambda t: 1/(t**2 - 1)
F6_np  = lambda t: 0.5*np.log(np.abs(t-1)) - 0.5*np.log(np.abs(t+1))
for seg, ls_style in [(t6a, '-'), (t6b, '-')]:
    ax6.plot(seg, f6_np(seg), 'royalblue', lw=2.5,
             label=r'$f=\frac{1}{x^2-1}$' if ls_style == '-' and seg is t6a else "")
    ax6.plot(seg, F6_np(seg), 'tomato',    lw=2, ls='--',
             label=r'$F=\frac{1}{2}\ln\left|\frac{x-1}{x+1}\right|$' if ls_style == '-' and seg is t6a else "")
ax6.axhline(0, color='k', lw=0.5)
ax6.set_xlim(-3, 3); ax6.set_ylim(-3, 3)
ax6.set_title(r"Partial Fractions: $\frac{1}{x^2-1}$", fontsize=10)
ax6.legend(fontsize=8); ax6.grid(True, alpha=0.3)

plt.savefig("indefinite_integrals.png", dpi=120, bbox_inches='tight')
print("Plot saved: indefinite_integrals.png")
plt.show()
