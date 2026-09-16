# ============================================================
# python_deriv_apps.py
# Κεφάλαιο 9 — Εφαρμογές Παραγώγου
# Ματζάκος, Ν. (2026). Στοιχεία Γραμμικής Άλγεβρας, Διαφορικού & Ολοκληρωτικού Λογισμού. NewTech Publications.
# ============================================================
#
# ΒΙΒΛΙΟΘΗΚΕΣ:
#   sympy         → κρίσιμα σημεία, βελτιστοποίηση, MVT
#   scipy.optimize→ minimize_scalar, brentq (αριθμητική βελτ/ση)
#   numpy         → αριθμητική εκτίμηση
#   matplotlib    → πλήρης ανάλυση συνάρτησης
#
# ΒΑΣΙΚΕΣ ΕΝΤΟΛΕΣ:
#   sympy.solve(diff(f,x), x)       → κρίσιμα σημεία
#   sympy.diff(f,x,2).subs(x,c)     → κριτήριο 2ης παρ.
#   scipy.optimize.minimize_scalar  → αριθμητικό ελάχιστο
#   scipy.optimize.brentq           → εύρεση ρίζας (Newton)
# ============================================================

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec
from sympy import (symbols, diff, solve, factor, simplify,
                   lambdify, Rational, sqrt, pi, exp, log,
                   pprint, sign)
from scipy.optimize import minimize_scalar, brentq, newton

x = symbols('x')

print("=" * 55)
print(" Κεφάλαιο 9: Εφαρμογές Παραγώγου — Python")
print("=" * 55)

# ── Α. Μονοτονία & Τοπικά Ακρότατα ──────────────────────
print("\n── Α. Μονοτονία & Τοπικά Ακρότατα ──")

f_sym  = x**3 - 3*x**2 - 9*x + 5
fp_sym = diff(f_sym, x)
fpp_sym= diff(f_sym, x, 2)

print(f"f(x)  = {f_sym}")
print(f"f'(x) = {factor(fp_sym)}  = 3(x-3)(x+1)")
print(f"f''(x)= {fpp_sym}")

crits = solve(fp_sym, x)
print(f"\nΚρίσιμα σημεία: {crits}")

for xc in crits:
    fc  = f_sym.subs(x, xc)
    sc  = fpp_sym.subs(x, xc)
    kind = "ΤΟΠΙΚΟ ΕΛΑΧΙΣΤΟ" if sc > 0 else "ΤΟΠΙΚΟ ΜΕΓΙΣΤΟ" if sc < 0 else "?"
    print(f"  x={xc}: f={fc}, f''={sc} → {kind}")

# Μονοτονία (αριθμητικά δείγματα)
print("\nΜονοτονία:")
test_pts = [(-3, "x=-3"), (0, "x=0"), (5, "x=5")]
f_np  = lambdify(x, f_sym,  'numpy')
fp_np = lambdify(x, fp_sym, 'numpy')
for xv, label in test_pts:
    print(f"  f'({xv}) = {fp_np(xv):.2f}  → {'αύξουσα ↑' if fp_np(xv)>0 else 'φθίνουσα ↓'}")

# ── Β. Κυρτότητα & Σημεία Καμπής ─────────────────────────
print("\n── Β. Κυρτότητα & Σημεία Καμπής ──")

inflect = solve(fpp_sym, x)
fpp_np  = lambdify(x, fpp_sym, 'numpy')
print(f"Σημεία καμπής (f''=0): {inflect}")
for xi in inflect:
    print(f"  ({xi}, {f_sym.subs(x,xi)})  "
          f"f'' αλλάζει πρόσημο → καμπή")

# ── Γ. Βελτιστοποίηση ─────────────────────────────────────
print("\n── Γ. Βελτιστοποίηση ──")

# Πρόβλημα 1: μέγιστο εμβαδόν ορθογωνίου P=20
E_sym = x * (10 - x)
Ep_sym= diff(E_sym, x)
x_opt = solve(Ep_sym, x)[0]
print(f"Ορθογώνιο (P=20):  x*={x_opt}, y*={10-x_opt}, E_max={E_sym.subs(x,x_opt)}")

# Αριθμητική επαλήθευση
E_np = lambdify(x, E_sym, 'numpy')
result = minimize_scalar(lambda v: -E_np(v), bounds=(0,10), method='bounded')
print(f"  scipy minimize_scalar: x*≈{result.x:.6f}, E_max≈{-result.fun:.6f}  ✓")

# Πρόβλημα 2: δοχείο ελαχίστης επιφάνειας (V=32)
S_sym = x**2 + 4*x*(32/x**2)
Sp_sym= diff(S_sym, x)
x_box = [s for s in solve(Sp_sym, x) if s.is_real and s > 0][0]
h_box = 32 / x_box**2
print(f"\nΔοχείο (V=32):  x*={float(x_box):.4f}, h*={float(h_box):.4f}")
print(f"  x=h*2? {abs(float(x_box) - 2*float(h_box)) < 0.01}")   # x=2h για κύβο

# ── Δ. Θεώρημα Μέσης Τιμής ───────────────────────────────
print("\n── Δ. Θεώρημα Μέσης Τιμής (MVT) ──")

f_mvt  = x**2 - x + 1
fp_mvt = diff(f_mvt, x)
a_m, b_m = 1, 4
slope = (f_mvt.subs(x,b_m) - f_mvt.subs(x,a_m)) / (b_m - a_m)
c_val = solve(fp_mvt - slope, x)[0]
print(f"f(x)=x²-x+1  στο [{a_m},{b_m}]")
print(f"Μέση κλίση = {slope},  c = {c_val}")
print(f"c ∈ ({a_m},{b_m}): {a_m < c_val < b_m}  ✓")

# ── Ε. Μέθοδος Newton-Raphson ─────────────────────────────
print("\n── Ε. Μέθοδος Newton-Raphson ──")

f_nr_sym  = x**3 - x - 2
fp_nr_sym = diff(f_nr_sym, x)
f_nr_np   = lambdify(x, f_nr_sym,  'numpy')
fp_nr_np  = lambdify(x, fp_nr_sym, 'numpy')

# Χειροκίνητη υλοποίηση Newton
xn = 1.5
print(f"f(x) = x³-x-2,  x₀={xn}")
for i in range(1, 7):
    xn_new = xn - f_nr_np(xn)/fp_nr_np(xn)
    print(f"  Επ.{i}: x={xn_new:.10f}  f(x)={f_nr_np(xn_new):.2e}")
    xn = xn_new

# scipy.optimize.newton
root = newton(f_nr_np, 1.5, fprime=fp_nr_np)
print(f"scipy.newton: x*={root:.10f}  ✓")

# ── Στ. Πλήρης Ανάλυση Συνάρτησης — Γραφικά ──────────────
print("\n── Στ. Γραφικές Παραστάσεις ──")

t = np.linspace(-3.5, 5.5, 800)

fig = plt.figure(figsize=(14, 9))
fig.suptitle("Εφαρμογές Παραγώγου", fontsize=13, fontweight='bold')
gs = gridspec.GridSpec(2, 3, fig)

# 1. Πλήρης ανάλυση f(x)=x³-3x²-9x+5
ax1 = fig.add_subplot(gs[0, :2])
ax1.plot(t, f_np(t),   'royalblue', lw=2.5, label='$f(x)=x^3-3x^2-9x+5$')
ax1.plot(t, fp_np(t),  'tomato',    lw=1.8, ls='--', label="$f'(x)$")
ax1.plot(t, fpp_np(t), 'forestgreen', lw=1.5, ls=':', label="$f''(x)$")
# Σημάνσεις ακροτάτων
for xc in crits:
    fc = float(f_sym.subs(x, xc))
    ax1.plot(float(xc), fc, 'ko', ms=8, zorder=5)
    ax1.annotate(f"({'max' if fpp_sym.subs(x,xc)<0 else 'min'})\n({float(xc):.0f},{fc:.0f})",
                 (float(xc), fc), textcoords="offset points", xytext=(8,8), fontsize=8)
# Σημείο καμπής
xi = float(inflect[0])
ax1.axvline(xi, color='gray', ls=':', lw=1, alpha=0.6)
ax1.axhline(0, color='k', lw=0.5)
ax1.set_xlim(-3.5, 5.5); ax1.set_ylim(-30, 25)
ax1.legend(fontsize=9); ax1.grid(True, alpha=0.3)
ax1.set_title("Πλήρης Ανάλυση: $f$, $f'$, $f''$", fontsize=10)

# 2. Βελτιστοποίηση εμβαδού
ax2 = fig.add_subplot(gs[0, 2])
xv = np.linspace(0, 10, 300)
ax2.plot(xv, E_np(xv), 'royalblue', lw=2.5)
ax2.axvline(float(x_opt), color='tomato', ls='--', lw=1.5,
            label=f'$x^*={float(x_opt):.0f}$')
ax2.plot(float(x_opt), float(E_sym.subs(x,x_opt)), 'ro', ms=8)
ax2.set_title("Βελτιστοποίηση: $E=x(10-x)$", fontsize=10)
ax2.set_xlabel('x'); ax2.set_ylabel('Εμβαδόν')
ax2.legend(fontsize=9); ax2.grid(True, alpha=0.3)

# 3. MVT
ax3 = fig.add_subplot(gs[1, 0])
f_mvt_np = lambdify(x, f_mvt, 'numpy')
tv = np.linspace(0, 5, 300)
ax3.plot(tv, f_mvt_np(tv), 'royalblue', lw=2.5, label='$f(x)=x^2-x+1$')
# Χορδή
xA, xB = float(a_m), float(b_m)
yA, yB = f_mvt_np(xA), f_mvt_np(xB)
ax3.plot([xA,xB],[yA,yB],'k--',lw=1.5,label='Χορδή')
# Εφαπτόμενη στο c
c_f = float(c_val)
tang_c = float(slope)*(tv - c_f) + f_mvt_np(c_f)
ax3.plot(tv, tang_c, 'tomato', lw=1.5, ls='-.', label=f'Εφαπτ. c={c_f:.1f}')
ax3.plot(c_f, f_mvt_np(c_f), 'ro', ms=7, zorder=5)
ax3.set_xlim(0,5); ax3.set_ylim(-1,15)
ax3.set_title("Θεώρημα Μέσης Τιμής", fontsize=10)
ax3.legend(fontsize=8); ax3.grid(True,alpha=0.3)

# 4. Newton-Raphson σύγκλιση
ax4 = fig.add_subplot(gs[1, 1])
tv2 = np.linspace(0.5, 2.5, 300)
ax4.plot(tv2, f_nr_np(tv2), 'royalblue', lw=2.5, label='$x^3-x-2$')
ax4.axhline(0, color='k', lw=0.8)
ax4.axvline(root, color='tomato', ls='--', lw=1.5, label=f'Ρίζα x*≈{root:.4f}')
# Βήματα Newton
xn = 1.5
for i in range(4):
    xn_new = xn - f_nr_np(xn)/fp_nr_np(xn)
    ax4.annotate('', xy=(xn_new, 0), xytext=(xn, f_nr_np(xn)),
                 arrowprops=dict(arrowstyle='->', color='forestgreen', lw=1.5))
    ax4.plot(xn, f_nr_np(xn), 'go', ms=6)
    xn = xn_new
ax4.set_title("Newton-Raphson $x^3-x-2=0$", fontsize=10)
ax4.legend(fontsize=8); ax4.grid(True,alpha=0.3)
ax4.set_xlim(0.5,2.5); ax4.set_ylim(-3,4)

# 5. Δοχείο βελτιστοποίηση
ax5 = fig.add_subplot(gs[1, 2])
xv3 = np.linspace(0.5, 5, 300)
S_np = lambdify(x, S_sym, 'numpy')
ax5.plot(xv3, S_np(xv3), 'royalblue', lw=2.5, label='$S(x)=x^2+128/x$')
ax5.axvline(float(x_box), color='tomato', ls='--', lw=1.5,
            label=f'$x^*≈{float(x_box):.3f}$')
ax5.plot(float(x_box), float(S_sym.subs(x,x_box)), 'ro', ms=8)
ax5.set_title("Δοχείο: Ελαχ. Επιφάνεια", fontsize=10)
ax5.set_xlabel('x'); ax5.set_ylabel('S(x)')
ax5.legend(fontsize=8); ax5.grid(True,alpha=0.3)
ax5.set_ylim(0,100)

plt.tight_layout()
plt.savefig("deriv_applications.png", dpi=120, bbox_inches='tight')
print("Το διάγραμμα αποθηκεύτηκε: deriv_applications.png")
plt.show()
