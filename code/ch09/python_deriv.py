# ============================================================
# python_deriv.py
# Κεφάλαιο 8 — Παράγωγος
# Ματζάκος, Ν. (2026). Στοιχεία Γραμμικής Άλγεβρας, Διαφορικού & Ολοκληρωτικού Λογισμού. NewTech Publications.
# ============================================================
#
# ΒΙΒΛΙΟΘΗΚΕΣ:
#   sympy      → συμβολική παραγώγιση (diff, simplify)
#   numpy      → αριθμητική παραγώγιση (gradient, central diff)
#   matplotlib → γραφικές παραστάσεις (f, f', f'', εφαπτόμενη)
#
# ΒΑΣΙΚΕΣ ΕΝΤΟΛΕΣ:
#   sympy.diff(f, x)      → f'(x)
#   sympy.diff(f, x, n)   → f⁽ⁿ⁾(x)
#   f_expr.subs(x, a)     → f(a)
#   sympy.lambdify(x, f)  → μετατροπή σε αριθμητική συνάρτηση
#   np.gradient(y, dx)    → αριθμητική παράγωγος
# ============================================================

import numpy as np
import matplotlib.pyplot as plt
from sympy import (symbols, diff, sin, cos, tan, exp, log, sqrt,
                   simplify, trigsimp, expand, limit, lambdify,
                   pprint, Rational, pi, oo)

x, h = symbols('x h')

print("=" * 55)
print(" Κεφάλαιο 8: Παράγωγος — Python")
print("=" * 55)

# ── Α. Βασικές Παράγωγοι ─────────────────────────────────
print("\n── Α. Βασικές Παράγωγοι ──")

funcs = [
    ("3x⁴ - 5x² + 2x - 7",  3*x**4 - 5*x**2 + 2*x - 7),
    ("sin(x)",               sin(x)),
    ("cos(x)",               cos(x)),
    ("tan(x)",               tan(x)),
    ("e^x",                  exp(x)),
    ("e^(3x)",               exp(3*x)),
    ("ln(x)",                log(x)),
    ("ln(x²+1)",             log(x**2+1)),
    ("x^x  (λογ. παράγ.)",  x**x),
]

for label, f in funcs:
    fp = simplify(diff(f, x))
    print(f"  d/dx[{label}] = {fp}")

# ── Β. Κανόνες Παραγώγισης ───────────────────────────────
print("\n── Β. Κανόνες Παραγώγισης ──")

f_prod = x**2 * sin(x)
f_quot = (x**3 + 1) / (x**2 - 1)
f_chain = sin(x**2 + 1)
f_comp  = exp(sin(x)**2)

print(f"  Κανόνας γινομένου: (x²·sin x)' = {expand(diff(f_prod, x))}")
print(f"  Κανόνας πηλίκου:   [(x³+1)/(x²-1)]' = {simplify(diff(f_quot, x))}")
print(f"  Κανόνας αλυσίδας:  [sin(x²+1)]' = {diff(f_chain, x)}")
print(f"  Σύνθετη:           [e^(sin²x)]' = {simplify(diff(f_comp, x))}")

# ── Γ. Ανώτερης Τάξης Παράγωγοι ──────────────────────────
print("\n── Γ. Ανώτερης Τάξης Παράγωγοι ──")

f_e = exp(x) * cos(x)
print("f(x) = eˣcos(x)")
for n in range(1, 5):
    dn = trigsimp(diff(f_e, x, n))
    print(f"  f{'⁽'+str(n)+'⁾'} = {dn}")
print(f"  f⁽⁴⁾ + 4f = {trigsimp(diff(f_e,x,4) + 4*f_e)}  (= 0 ✓)")

# ── Δ. Παράγωγος με Ορισμό ───────────────────────────────
print("\n── Δ. Παράγωγος μέσω Ορισμού ──")

for f_def, label in [(x**2, "x²"), (sqrt(x), "√x"), (sin(x), "sin(x)")]:
    fp_def = limit((f_def.subs(x, x+h) - f_def) / h, h, 0)
    print(f"  d/dx[{label}] = {simplify(fp_def)}")

# ── Ε. Εφαπτόμενη & Κάθετη Ευθεία ───────────────────────
print("\n── Ε. Εφαπτόμενη Ευθεία ──")

f_tan_sym = x**3 - 2*x + 1
x0 = 1
y0 = f_tan_sym.subs(x, x0)
m  = diff(f_tan_sym, x).subs(x, x0)
print(f"  f(x) = x³-2x+1,  x₀={x0}")
print(f"  f(x₀)={y0},  f'(x₀)={m}")
print(f"  Εφαπτόμενη: y = {m}(x-{x0}) + {y0}  =  {m}x + {y0-m*x0}")
print(f"  Κάθετη:     y = {-1/m}(x-{x0}) + {y0}")

# ── Στ. Αριθμητική Παραγώγιση (NumPy) ────────────────────
print("\n── Στ. Αριθμητική Παραγώγιση (NumPy) ──")

t = np.linspace(0.01, 2*np.pi, 1000)
dt = t[1] - t[0]
f_num   = np.sin(t)
fp_num  = np.gradient(f_num, dt)         # αριθμητική παράγωγος
fp_exact = np.cos(t)                     # ακριβής

error = np.max(np.abs(fp_num - fp_exact))
print(f"  Μέγιστο σφάλμα αριθμητικής παραγώγου sin(x): {error:.2e}  ✓")

# ── Ζ. Γραφικές Παραστάσεις ──────────────────────────────
print("\n── Ζ. Γραφικές Παραστάσεις ──")

# Μετατροπή sympy → numpy
f_np  = lambdify(x, f_tan_sym,          'numpy')
fp_np = lambdify(x, diff(f_tan_sym, x), 'numpy')
fpp_np= lambdify(x, diff(f_tan_sym, x, 2), 'numpy')

fig, axes = plt.subplots(1, 3, figsize=(14, 4.5))
fig.suptitle("Παράγωγος — Γραφικές Παραστάσεις", fontsize=13, fontweight='bold')

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

# --- Εφαπτόμενη ---
ax2 = axes[1]
tang = float(m)*(t2 - x0) + float(y0)
ax2.plot(t2, f_np(t2), 'royalblue', lw=2.5, label='$f(x)$')
ax2.plot(t2, tang,     'tomato', lw=1.8, ls='--', label=f'Εφαπτόμενη x₀={x0}')
ax2.plot(x0, float(y0), 'ko', ms=7, zorder=5)
ax2.set_title("Εφαπτόμενη στο $x_0=1$", fontsize=10)
ax2.legend(fontsize=8); ax2.grid(True,alpha=0.3)
ax2.set_xlim(-2,2.5); ax2.set_ylim(-4,6)

# --- Αριθμητική vs Ακριβής παράγωγος ---
ax3 = axes[2]
ax3.plot(t, fp_exact, 'royalblue', lw=2.5, label='cos(x) (ακριβής)')
ax3.plot(t, fp_num,   'tomato', lw=1.5, ls='--', label="np.gradient (αριθμ.)")
ax3.set_title("Αριθμητική vs Ακριβής παράγωγος\n$f(x)=\\sin(x)$", fontsize=10)
ax3.legend(fontsize=8); ax3.grid(True,alpha=0.3)

plt.tight_layout()
plt.savefig("derivatives.png", dpi=120, bbox_inches='tight')
print("Το διάγραμμα αποθηκεύτηκε: derivatives.png")
plt.show()
