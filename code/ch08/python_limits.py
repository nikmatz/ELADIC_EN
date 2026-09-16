# ============================================================
# python_limits.py
# Κεφάλαιο 7 — Συναρτήσεις, Όρια και Συνέχεια
# Ματζάκος, Ν. (2026). Στοιχεία Γραμμικής Άλγεβρας, Διαφορικού & Ολοκληρωτικού Λογισμού. NewTech Publications.
# ============================================================
#
# ΒΙΒΛΙΟΘΗΚΕΣ:
#   sympy      → συμβολικός υπολογισμός ορίων (limit)
#   numpy      → αριθμητική προσέγγιση (για εποπτεία)
#   matplotlib → γραφικές παραστάσεις, οπτικοποίηση ορίων
#
# ΒΑΣΙΚΕΣ ΕΝΤΟΛΕΣ:
#   sympy.limit(f, x, a)           → lim_{x→a} f(x)
#   sympy.limit(f, x, a, '+')      → μονόπλευρο x→a⁺
#   sympy.limit(f, x, oo)          → lim_{x→+∞}
#   sympy.series(f, x, a, n)       → ανάπτυγμα Taylor/Maclaurin
#   sympy.is_continuous_at(f, a)   → συνέχεια (μέσω limit)
# ============================================================

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec
from sympy import (symbols, limit, sin, cos, exp, log, Abs,
                   sqrt, oo, pi, Rational, series, factorial,
                   pprint, simplify, floor)

x = symbols('x')

print("=" * 55)
print(" Κεφάλαιο 7: Συναρτήσεις, Όρια, Συνέχεια — Python")
print("=" * 55)

# ── Α. Υπολογισμός Ορίων (SymPy) ─────────────────────────
print("\n── Α. Υπολογισμός Ορίων ──")

limits_table = [
    ("lim_{x→2} (x²+3x-1)",          x**2+3*x-1,          x, 2,    None),
    ("lim_{x→3} (x²-9)/(x-3)",       (x**2-9)/(x-3),      x, 3,    None),
    ("lim_{x→0} sin(x)/x",           sin(x)/x,             x, 0,    None),
    ("lim_{x→0} (1-cos x)/x²",       (1-cos(x))/x**2,     x, 0,    None),
    ("lim_{x→0} (eˣ-1)/x",           (exp(x)-1)/x,        x, 0,    None),
    ("lim_{x→0⁺} x·ln(x)",           x*log(x),             x, 0,    '+'),
    ("lim_{x→+∞} (3x²-2x+1)/(x²+5)",(3*x**2-2*x+1)/(x**2+5), x, oo, None),
    ("lim_{x→+∞} (1+1/x)^x",        (1+1/x)**x,          x, oo,   None),
]

for label, f, var, pt, side in limits_table:
    if side:
        val = limit(f, var, pt, side)
    else:
        val = limit(f, var, pt)
    print(f"  {label} = {val}")

# ── Β. Μονόπλευρα Όρια ───────────────────────────────────
print("\n── Β. Μονόπλευρα Όρια ──")

f_sign = Abs(x)/x
lp = limit(f_sign, x, 0, '+')
lm = limit(f_sign, x, 0, '-')
print(f"  lim_{{x→0⁺}} |x|/x = {lp}")
print(f"  lim_{{x→0⁻}} |x|/x = {lm}")
print(f"  lp ≠ lm → δεν υπάρχει lim_{{x→0}}  ✓")

print(f"  lim_{{x→0⁺}} 1/x = {limit(1/x, x, 0, '+')}")
print(f"  lim_{{x→0⁻}} 1/x = {limit(1/x, x, 0, '-')}")

# ── Γ. Έλεγχος Συνέχειας ─────────────────────────────────
print("\n── Γ. Συνέχεια ──")

def check_continuity(f_expr, a, f_at_a, label="f"):
    """Ελέγχει αν f είναι συνεχής στο a."""
    lval = limit(f_expr, x, a)
    cont = (lval == f_at_a)
    print(f"  {label}: lim_{{x→{a}}} = {lval},  f({a}) = {f_at_a}")
    print(f"  Συνεχής: {cont}")
    return cont

# (x²-4)/(x-2) με f(2)=4
f1 = (x**2 - 4)/(x - 2)
check_continuity(f1, 2, 4, "f(x)=(x²-4)/(x-2),  f(2)=4")

# sin(x)/x με f(0)=1
check_continuity(sin(x)/x, 0, 1, "g(x)=sin(x)/x,  g(0)=1")

# Ασυνεχής: ορίζεται f(0)=0 αλλά lim ≠ 0 (δεν υπάρχει)
print(f"\n  h(x)=|x|/x: lim_{{x→0}} δεν υπάρχει → ασυνεχής στο 0")

# ── Δ. Κανόνας L'Hôpital ─────────────────────────────────
print("\n── Δ. L'Hôpital ──")

lhopital_cases = [
    ("(x³-8)/(x²-4)", (x**3-8)/(x**2-4), x, 2),
    ("ln(x)/x",       log(x)/x,           x, oo),
    ("x·e^(-x)",      x*exp(-x),          x, oo),
    ("(sin x - x)/x³",  (sin(x)-x)/x**3, x, 0),
]

for label, f, var, pt in lhopital_cases:
    val = limit(f, var, pt)
    print(f"  lim_{{x→{pt}}} {label} = {val}")

# ── Ε. Ανάπτυγμα Taylor/Maclaurin ────────────────────────
print("\n── Ε. Αναπτύγματα Maclaurin ──")

funcs_taylor = [
    ("sin(x)",   sin(x),      6),
    ("cos(x)",   cos(x),      6),
    ("e^x",      exp(x),      5),
    ("ln(1+x)",  log(1+x),    5),
    ("1/(1-x)",  1/(1-x),     5),
]

for label, f, n in funcs_taylor:
    s = series(f, x, 0, n)
    print(f"  {label} = {s}")

# ── Στ. Γραφικές Παραστάσεις ─────────────────────────────
print("\n── Στ. Γραφικές Παραστάσεις ──")

fig = plt.figure(figsize=(14, 9))
fig.suptitle("Συναρτήσεις, Όρια και Συνέχεια", fontsize=13, fontweight='bold')
gs = gridspec.GridSpec(2, 3, fig)

# 1. sin(x)/x  → 1
ax1 = fig.add_subplot(gs[0, 0])
t = np.linspace(-4*np.pi, 4*np.pi, 1000)
t_nz = t[t != 0]
ax1.plot(t_nz, np.sin(t_nz)/t_nz, 'royalblue', lw=2)
ax1.plot(0, 1, 'ro', ms=7, label='lim=1')
ax1.axhline(0,color='k',lw=0.4); ax1.axhline(1,color='tomato',ls='--',lw=1,alpha=0.6)
ax1.set_title(r'$\frac{\sin x}{x} \to 1$', fontsize=10)
ax1.set_ylim(-0.5,1.3); ax1.grid(True,alpha=0.3); ax1.legend(fontsize=8)

# 2. (1+1/x)^x → e
ax2 = fig.add_subplot(gs[0, 1])
t2 = np.logspace(0, 4, 300)
ax2.semilogx(t2, (1+1/t2)**t2, 'royalblue', lw=2)
ax2.axhline(np.e, color='tomato', ls='--', lw=1.5, label=f'e≈{np.e:.4f}')
ax2.set_title(r'$(1+\frac{1}{x})^x \to e$', fontsize=10)
ax2.set_xlabel('x (log scale)'); ax2.grid(True,alpha=0.3); ax2.legend(fontsize=8)

# 3. Μονόπλευρα: |x|/x
ax3 = fig.add_subplot(gs[0, 2])
t3p = np.linspace(0.01, 3, 200)
t3m = np.linspace(-3, -0.01, 200)
ax3.plot(t3p, np.ones_like(t3p),  'royalblue', lw=2.5, label='x>0: lim=+1')
ax3.plot(t3m, -np.ones_like(t3m), 'tomato',    lw=2.5, label='x<0: lim=-1')
ax3.plot(0, 1,  'o', color='royalblue', ms=8, mfc='white', mew=2)
ax3.plot(0, -1, 'o', color='tomato',    ms=8, mfc='white', mew=2)
ax3.axhline(0,color='k',lw=0.4); ax3.axvline(0,color='k',lw=0.4)
ax3.set_title(r'$|x|/x$ — άλμα στο 0', fontsize=10)
ax3.set_ylim(-2,2); ax3.grid(True,alpha=0.3); ax3.legend(fontsize=8)

# 4. Taylor sin(x) vs πολυώνυμα
ax4 = fig.add_subplot(gs[1, 0:2])
t4 = np.linspace(-2*np.pi, 2*np.pi, 500)
ax4.plot(t4, np.sin(t4), 'k', lw=2.5, label='sin(x)')
colors4 = ['#e74c3c','#e67e22','#27ae60','#2980b9']
for n, col in zip([1, 3, 5, 7], colors4):
    p = sum((-1)**k * t4**(2*k+1) / np.math.factorial(2*k+1) for k in range((n+1)//2 + 1))
    # Clip for visual clarity
    p_clipped = np.clip(p, -3, 3)
    ax4.plot(t4, p_clipped, color=col, lw=1.5, ls='--', label=f'Taylor n={n}')
ax4.set_ylim(-2.5, 2.5); ax4.set_title("Προσέγγιση Taylor: sin(x)", fontsize=10)
ax4.legend(fontsize=8, loc='upper right'); ax4.grid(True,alpha=0.3)

# 5. Συνεχής vs ασυνεχής
ax5 = fig.add_subplot(gs[1, 2])
t5 = np.linspace(-2, 4, 500)
# Τμηματικά ορισμένη: f(x) = x² αν x<1, 2x+1 αν x≥1
f5 = np.where(t5 < 1, t5**2, 2*t5+1)
ax5.plot(t5, f5, 'royalblue', lw=2)
ax5.plot(1, 1,  'o', color='royalblue', ms=8, mfc='white', mew=2, label='x<1: $x^2$')
ax5.plot(1, 3,  'o', color='tomato',    ms=8, mfc='tomato', mew=2, label='x≥1: $2x+1$')
ax5.axvline(1, color='gray', ls=':', lw=1)
ax5.set_title("Ασυνεχής στο $x=1$", fontsize=10)
ax5.set_ylim(-1, 10); ax5.grid(True,alpha=0.3); ax5.legend(fontsize=8)

plt.tight_layout()
plt.savefig("limits_continuity.png", dpi=120, bbox_inches='tight')
print("Το διάγραμμα αποθηκεύτηκε: limits_continuity.png")
plt.show()
