# ============================================================
# python_texnikes.py
# Chapter 16 — Techniques of Integration
# Matzakos, N. (2026). Elements of Linear Algebra, Differential & Integral Calculus. NewTech Publications.
# ------------------------------------------------------------
# BASIC COMMANDS:
#   sympy.integrate(f, x)                  -> integration
#   sympy.apart(f, x)                      -> partial fractions
#   sympy.integrals.manualintegrate(f, x)  -> "textbook" techniques
#   sympy.integrals.integral_steps(f, x)   -> which rule it chose
#   sympy.trigsimp(), sympy.simplify()     -> simplification
#   scipy.integrate.quad(f, a, b)          -> numerical integral
# ============================================================
import sympy as sp
import numpy as np
import matplotlib.pyplot as plt
from sympy.integrals.manualintegrate import manualintegrate, integral_steps
from scipy.integrate import quad

x = sp.symbols('x', positive=True)

print("=" * 62)
print(" Chapter 16: Techniques of Integration")
print("=" * 62)


# ------------------------------------------------------------
# Helper verification function (asked for in part (a)):
#   F is an antiderivative of f  <=>  simplify(F' - f) == 0
# ------------------------------------------------------------
def check(F, f):
    """True if F is an antiderivative of f."""
    return sp.simplify(sp.diff(F, x) - f) == 0


# ============================================================
# A. SUBSTITUTION
#    The same integrals as in the Maxima activity.
# ============================================================
print("\n=== A. SUBSTITUTION ===")
print("f(x)                  substitution    int f dx")

antikat = [
    (x * sp.exp(x**2),      "u = x^2",    sp.exp(x**2) / 2),
    (x / sp.sqrt(x**2 + 4), "u = x^2+4",  sp.sqrt(x**2 + 4)),
    (sp.log(x) / x,         "u = ln x",   sp.log(x)**2 / 2),
]

for f, subst, anamenomeno in antikat:
    F = sp.integrate(f, x)
    print(f"  {str(f):20s}  {subst:11s}  {F}  + C")
    print(f"      check(F, f) = {check(F, f)}"
          f"   |  expected {anamenomeno}: "
          f"{sp.simplify(F - anamenomeno) == 0}")


# ============================================================
# B. INTEGRATION BY PARTS — which technique does SymPy choose?
#    manualintegrate follows the "textbook" techniques, while
#    integral_steps returns the tree of rules it used.
# ============================================================
print("\n=== B. INTEGRATION BY PARTS (manualintegrate) ===")

kata_meri = [
    (x**2 * sp.exp(x),      "applied twice: u=x^2, dv=e^x dx"),
    (sp.atan(x),            "u = arctan x, dv = dx"),
    (sp.exp(x) * sp.sin(x), "cyclic: the integral reappears"),
]

for f, dikh_mas in kata_meri:
    F = sp.simplify(manualintegrate(f, x))
    kanonas = type(integral_steps(f, x)).__name__
    print(f"\n  ∫ {f} dx = {F} + C")
    print(f"      SymPy rule      : {kanonas}")
    print(f"      our own choice  : {dikh_mas}")
    print(f"      check(F, f)   : {check(F, f)}")

# The cyclic case in "textbook" form e^x*(sin x - cos x)/2
F_kyk = sp.simplify(manualintegrate(sp.exp(x) * sp.sin(x), x))
sxolikh = sp.exp(x) * (sp.sin(x) - sp.cos(x)) / 2
print(f"\n  Textbook form e^x*(sin x - cos x)/2 same as SymPy: "
      f"{sp.simplify(F_kyk - sxolikh) == 0}")


# ============================================================
# C. PARTIAL FRACTIONS — apart and term-by-term integration
# ============================================================
print("\n=== C. PARTIAL FRACTIONS (apart) ===")

ritles = [
    (2*x + 3) / (x**2 - x - 2),
    (2*x**2 - 1) / (x * (x + 1)**2),
    (x**3 - 1) / (x**2 + x + 1),
]

for f in ritles:
    pf = sp.apart(f, x)
    oroi = sp.Add.make_args(pf)
    athroisma = sp.Add(*[sp.integrate(t, x) for t in oroi])
    ameso = sp.integrate(f, x)
    print(f"\n  f(x) = {f}")
    print(f"      apart        : {pf}")
    # expand_log: shows the logarithms explicitly, not collapsed
    print(f"      term by term : {sp.expand_log(sp.expand(athroisma), force=True)} + C")
    print(f"      direct       : {sp.expand_log(sp.expand(ameso), force=True)} + C")
    # Two antiderivatives agree if they differ at most by a constant,
    # that is, if the derivative of their difference is zero.
    print(f"      differ at most by a constant  : "
          f"{sp.simplify(sp.diff(athroisma - ameso, x)) == 0}")
    print(f"      identical expressions         : "
          f"{sp.simplify(athroisma - ameso) == 0}")
    print(f"      check(direct, f)              : {check(ameso, f)}")

# The third rational function has numerator degree >= denominator degree:
# polynomial division is needed FIRST.
phliko, ypoloipo = sp.div(x**3 - 1, x**2 + x + 1, x)
print(f"\n  Polynomial division: (x^3-1) : (x^2+x+1) -> "
      f"quotient {phliko}, remainder {ypoloipo}")
print(f"  Factorization       : x^3-1 = {sp.factor(x**3 - 1)}")


# ============================================================
# D. TRIGONOMETRIC SUBSTITUTION — symbolic vs numerical
#    ∫_0^1 sqrt(x^2+1) dx   (with x = tan(th))
# ============================================================
print("\n=== D. TRIGONOMETRIC SUBSTITUTION ===")

f_d = sp.sqrt(x**2 + 1)
F_d = sp.integrate(f_d, x)
print(f"  ∫ sqrt(x^2+1) dx = {F_d} + C")
print(f"      check(F, f) = {check(F_d, f_d)}")

symvolika = sp.integrate(f_d, (x, 0, 1))
kleisto = sp.sqrt(2)/2 + sp.log(1 + sp.sqrt(2))/2      # sqrt2/2 + ln(1+sqrt2)/2
print(f"\n  ∫_0^1 sqrt(x^2+1) dx = {symvolika}")
print(f"      closed form sqrt(2)/2 + ln(1+sqrt(2))/2 : "
      f"{sp.simplify(symvolika - kleisto) == 0}")

sym_val = float(symvolika)
num_val, sfalma = quad(lambda t: np.sqrt(t**2 + 1), 0, 1)
apoklisi = abs(sym_val - num_val)
print(f"      symbolic           = {sym_val:.12f}   (expected 1.147793574696)")
print(f"      scipy quad         = {num_val:.12f}   (est. error {sfalma:.1e})")
print(f"      |deviation|        = {apoklisi:.2e}")
print(f"      deviation < 1e-8   : {apoklisi < 1e-8}")

# --- Shaded region -------------------------------------------
xv = np.linspace(-0.3, 1.3, 400)
yv = np.sqrt(xv**2 + 1)
xs = np.linspace(0, 1, 200)
ys = np.sqrt(xs**2 + 1)

plt.figure(figsize=(7, 4.2))
plt.plot(xv, yv, 'b-', lw=2, label=r'$y=\sqrt{x^2+1}$')
plt.fill_between(xs, 0, ys, alpha=0.30, color='tab:green',
                 label=f'area = {sym_val:.6f}')
plt.axhline(0, color='k', lw=0.6)
plt.axvline(0, color='k', lw=0.6)
plt.xlim(-0.3, 1.3)
plt.ylim(0, 1.7)
plt.xlabel('x')
plt.ylabel('y')
plt.title(r'$\int_0^1\sqrt{x^2+1}\,dx$  (trigonometric substitution $x=\tan\theta$)')
plt.legend(loc='lower right')
plt.grid(True, alpha=0.3)
plt.tight_layout()

print("\nCompleted.")
plt.show()
