# python_genikeum.py — Improper Integrals (Ch. 18)
# Matzakos, N. (2026). Elements of Linear Algebra, Differential & Integral Calculus. NewTech Publications.
# Commands: sp.integrate(f,(x,1,sp.oo)), scipy.integrate.quad, scipy.special.gamma, sp.oo

import numpy as np
import sympy as sp
import matplotlib.pyplot as plt
from scipy.integrate import quad
from scipy.special import gamma as Gamma, beta as Beta
import math

x = sp.symbols('x', positive=True)

print("=" * 60)
print("IMPROPER INTEGRALS")
print("=" * 60)

# ── A. The p-test for type I improper integrals ──────────────────────────────
print()
print("A. ∫_1^∞ x^(-p) dx  —  symbolically with SymPy")
print("-" * 60)
for p in [sp.Rational(1, 2), sp.Integer(1), sp.Integer(2)]:
    I = sp.integrate(x**(-p), (x, 1, sp.oo))
    status = "converges" if I.is_finite else "diverges"
    print(f"   p = {str(p):3s} :  ∫ = {str(I):12s}  ({status})")
print("   Conclusion: it converges EXACTLY when p > 1.")
print("   (expected: p=1/2 -> oo, p=1 -> oo, p=2 -> 1)")

# ── B. The Gauss integral numerically ───────────────────────────────────────
print()
print("B. ∫_0^∞ e^(-x²) dx  —  numerically with scipy.integrate.quad")
print("-" * 60)
val, err = quad(lambda t: np.exp(-t**2), 0, np.inf)
exact = np.sqrt(np.pi) / 2
print(f"   quad          = {val:.15f}   (est. error {err:.1e})")
print(f"   √pi/2         = {exact:.15f}")
print(f"   |difference|  = {abs(val - exact):.3e}   (within double precision)")
print(f"   SymPy symbolically: {sp.integrate(sp.exp(-x**2), (x, 0, sp.oo))}")

# ── C. The Gamma function ───────────────────────────────────────────────────
print()
print("C. THE GAMMA FUNCTION:  Gamma(s) = ∫_0^∞ x^(s-1) e^(-x) dx")
print("-" * 60)
print(f"   Gamma(5) = {Gamma(5):.10f}   4! = {math.factorial(4)}   equal: {Gamma(5) == math.factorial(4)}")
print(f"   Gamma(1/2) = {Gamma(0.5):.12f}   √pi = {np.sqrt(np.pi):.12f}")
print(f"   Gamma(5/2) = {Gamma(2.5):.12f}   3√pi/4 = {3*np.sqrt(np.pi)/4:.12f}")
print(f"   B(2,3) = {Beta(2.0, 3.0):.12f}   Gamma(2)Gamma(3)/Gamma(5) = "
      f"{Gamma(2.0)*Gamma(3.0)/Gamma(5.0):.12f}   (1/12 = {1/12:.12f})")
print("   Definition through the integral (quad):")
for s in (0.5, 2.5, 5.0):
    I, _ = quad(lambda t, s=s: t**(s - 1) * np.exp(-t), 0, np.inf)
    print(f"      s = {s:3.1f} :  ∫ = {I:.10f}   Gamma(s) = {Gamma(s):.10f}")

# ── D. Optional: type II improper integrals ∫_0^1 x^(-p) dx ─────────────────
print()
print("D. (Optional) ∫_0^1 x^(-p) dx  —  type II, singular point at x=0")
print("-" * 60)
for p in [sp.Rational(1, 2), sp.Integer(1), sp.Integer(2)]:
    I = sp.integrate(x**(-p), (x, 0, 1))
    status = "converges" if I.is_finite else "diverges"
    print(f"   p = {str(p):3s} :  ∫ = {str(I):12s}  ({status})")
print("   Conclusion: it converges EXACTLY when p < 1.")
print("   (expected: p=1/2 -> 2, p=1 -> oo, p=2 -> oo)")
print()
print("   SUMMARY:")
print("     ∫_1^∞ x^(-p) dx  converges  <=>  p > 1   (tail at infinity)")
print("     ∫_0^1 x^(-p) dx  converges  <=>  p < 1   (singularity at 0)")
print("     No value of p makes both of them converge at the same time,")
print("     hence ∫_0^∞ x^(-p) dx diverges for every p.")

# ── Plots ───────────────────────────────────────────────────────────────────
fig, axes = plt.subplots(1, 2, figsize=(11, 4))

xv = np.linspace(1, 10, 500)
axes[0].plot(xv, 1 / xv**2, 'b-', label=r'$1/x^2$ (converges)')
axes[0].fill_between(xv, 1 / xv**2, alpha=0.25, color='blue')
axes[0].plot(xv, 1 / xv, 'r-', label=r'$1/x$ (diverges)')
axes[0].plot(xv, 1 / np.sqrt(xv), 'g--', label=r'$1/\sqrt{x}$ (diverges)')
axes[0].set_ylim(0, 1.2)
axes[0].set_xlabel('x')
axes[0].legend(fontsize=8)
axes[0].set_title(r"Type I: $\int_1^\infty x^{-p}dx$")
axes[0].grid(True, alpha=0.3)

xv2 = np.linspace(0.005, 1, 600)
axes[1].plot(xv2, 1 / np.sqrt(xv2), 'g-', label=r'$1/\sqrt{x}$ (converges)')
axes[1].fill_between(xv2, 1 / np.sqrt(xv2), alpha=0.25, color='green')
axes[1].plot(xv2, 1 / xv2, 'r-', label=r'$1/x$ (diverges)')
axes[1].set_ylim(0, 20)
axes[1].set_xlabel('x')
axes[1].legend(fontsize=8)
axes[1].set_title(r"Type II: $\int_0^1 x^{-p}dx$")
axes[1].grid(True, alpha=0.3)
plt.tight_layout()

# Plot of Gamma(x) on (0,5]  (part c)
plt.figure(figsize=(7, 4.5))
xg = np.linspace(0.05, 5.0, 800)
plt.plot(xg, Gamma(xg), 'b-', lw=2, label=r'$\Gamma(x)$')
ints = np.array([1, 2, 3, 4, 5])
plt.plot(ints, Gamma(ints.astype(float)), 'ro',
         label=r'$\Gamma(n)=(n-1)!$')
for m in ints:
    plt.annotate(f'{math.factorial(m - 1)}', (m, Gamma(float(m))),
                 textcoords='offset points', xytext=(6, 4), fontsize=8)
plt.axvline(0, color='gray', lw=0.8)
plt.ylim(0, 26)
plt.xlim(0, 5.2)
plt.xlabel('x')
plt.ylabel(r'$\Gamma(x)$')
plt.title(r'The function $\Gamma(x)$ on $(0,5]$ — it blows up as $x\to 0^+$')
plt.grid(True, alpha=0.3)
plt.legend()
plt.tight_layout()
plt.show()
