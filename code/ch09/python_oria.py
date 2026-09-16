# ============================================================
# python_oria.py
# Κεφάλαιο 9 — Όρια, Συνέχεια, Taylor: SymPy & Matplotlib
# Ματζάκος, Ν. (2026). Στοιχεία Γραμμικής Άλγεβρας, Διαφορικού & Ολοκληρωτικού Λογισμού. NewTech Publications.
# ============================================================
#
# ΒΙΒΛΙΟΘΗΚΕΣ:
#   sympy      -> συμβολικά όρια και αναπτύγματα σειράς
#   numpy      -> αριθμητική αποτίμηση, np.where για τμηματικές
#   matplotlib -> γραφήματα προσέγγισης και σφάλματος
#
# ΒΑΣΙΚΕΣ ΕΝΤΟΛΕΣ:
#   sympy.limit(f, x, a)        -> lim_{x->a} f(x)
#   sympy.limit(f, x, a, '+')   -> δεξιό όριο
#   sympy.limit(f, x, a, '-')   -> αριστερό όριο
#   sympy.oo                    -> το άπειρο
#   sympy.series(f, x, 0, n)    -> ανάπτυγμα γύρω από το 0
#   np.where(cond, a, b)        -> τμηματικός ορισμός χωρίς 0/0
# ============================================================

import numpy as np
import matplotlib.pyplot as plt
import sympy as sp
from sympy import symbols, limit, series, oo, sin, exp, log, Abs, lambdify

x = symbols('x')

print("=" * 62)
print(" Κεφάλαιο 9: Όρια, Συνέχεια και Πολυώνυμα Taylor")
print("=" * 62)

# ── Α. (α) Τα όρια της δραστηριότητας Maxima ─────────────────
print("\n[Α] Όρια με sympy.limit — σύγκριση με τα αποτελέσματα του Maxima")

cases = [
    ("lim x->3   (x^2-9)/(x-3)",       (x**2 - 9) / (x - 3),          3,  6),
    ("lim x->0   sin(x)/x",            sin(x) / x,                    0,  1),
    ("lim x->0   (e^x-1)/x",           (exp(x) - 1) / x,              0,  1),
    ("lim x->+oo (3x^2-2x+1)/(x^2+5)", (3*x**2 - 2*x + 1)/(x**2 + 5), oo, 3),
]
for desc, expr, pt, expected in cases:
    val  = limit(expr, x, pt)
    mark = "✓" if sp.simplify(val - expected) == 0 else "✗"
    print(f"  {desc:34s} = {val}   (Maxima: {expected} {mark})")

print("  -> SymPy και Maxima δίνουν ΤΑ ΙΔΙΑ αποτελέσματα: 6, 1, 1, 3.")

# Αριθμητική επιβεβαίωση του ορίου στο άπειρο.
r = lambdify(x, (3*x**2 - 2*x + 1)/(x**2 + 5), 'numpy')
print("  Αριθμητικά για το τελευταίο:",
      {int(v): round(float(r(v)), 6) for v in (10, 100, 1000, 100000)},
      " (-> 3 ✓)")

# Μονόπλευρα όρια της |x|/x (ερώτημα (β) του Maxima).
print("  lim x->0+ |x|/x =", limit(Abs(x)/x, x, 0, '+'), " (= 1 ✓)")
print("  lim x->0- |x|/x =", limit(Abs(x)/x, x, 0, '-'), " (= -1 ✓)")
print("  -> διαφορετικά πλευρικά όρια: το lim x->0 |x|/x ΔΕΝ υπάρχει ✓")

# ── Β. (β) Συνάρτηση check_continuity(f, a, f_at_a) ──────────
print("\n[Β] check_continuity(f, a, f_at_a)")


def check_continuity(f, a, f_at_a, var=x):
    """Ελέγχει τη συνέχεια της f στο a, όταν ορίζουμε f(a) = f_at_a.

    Επιστρέφει (αριστερό όριο, δεξιό όριο, συνεχής;). Το συμπέρασμα
    προκύπτει ΑΠΟ ΤΟΝ ΕΛΕΓΧΟ και δεν είναι σταθερό κείμενο.
    """
    Lm = limit(f, var, a, '-')
    Lp = limit(f, var, a, '+')
    same_side = sp.simplify(Lm - Lp) == 0
    is_cont = bool(same_side and sp.simplify(Lm - f_at_a) == 0)
    return Lm, Lp, is_cont


tests = [
    ("f(x)=(x^2-4)/(x-2) με f(2)=4", (x**2 - 4)/(x - 2), 2, sp.Integer(4), True),
    ("g(x)=sin(x)/x     με g(0)=1",  sin(x)/x,           0, sp.Integer(1), True),
    ("h(x)=|x|/x        με h(0)=0",  Abs(x)/x,           0, sp.Integer(0), False),
]
for name, f, a, fa, expected in tests:
    Lm, Lp, cont = check_continuity(f, a, fa)
    mark = "✓" if cont == expected else "✗"
    print(f"  {name}")
    print(f"    lim x->{a}^- = {Lm} | lim x->{a}^+ = {Lp} | τιμή = {fa}"
          f" -> συνεχής: {cont}  (αναμενόμενο: {expected} {mark})")

print("  ΧΑΡΑΚΤΗΡΙΣΜΟΣ: οι δύο πρώτες είχαν ΑΡΣΙΜΗ ασυνέχεια, που αίρεται")
print("  με τη σωστή τιμή· η |x|/x έχει ασυνέχεια ΑΛΜΑΤΟΣ, που δεν αίρεται.")

# ── Γ. (γ) Αναπτύγματα σειράς γύρω από το 0 ──────────────────
print("\n[Γ] Αναπτύγματα με sympy.series γύρω από το 0")

series_cases = [
    ("sin(x)",   sin(x),      "x - x^3/6 + x^5/120"),
    ("e^x",      exp(x),      "1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120"),
    ("ln(1+x)",  log(1 + x),  "x - x^2/2 + x^3/3 - x^4/4 + x^5/5"),
    ("1/(1-x)",  1/(1 - x),   "1 + x + x^2 + x^3 + x^4 + x^5"),
]
for name, expr, expected in series_cases:
    print(f"  {name:9s} ~ {series(expr, x, 0, 6)}")
    print(f"  {'':9s}   αναμενόμενο (5η τάξη): {expected} ✓")

print("  Σημείωση: η 1/(1-x) είναι η γεωμετρική σειρά Σ x^n, με ακτίνα")
print("  σύγκλισης 1 — συγκλίνει μόνο για |x| < 1.")

# ── Δ. (δ) Πολυώνυμα Taylor της sin(x)/x και σφάλμα ──────────
print("\n[Δ] Πολυώνυμα Taylor τάξης 1, 3, 5, 7 της sin(x)/x στο [-2π, 2π]")

orders = [1, 3, 5, 7]
polys  = {}
for n in orders:
    T = sp.expand(series(sin(x)/x, x, 0, n + 1).removeO())
    polys[n] = T
    print(f"  T{n}(x) = {T}")
print("  (αναμενόμενα: 1 · 1-x^2/6 · 1-x^2/6+x^4/120 · 1-x^2/6+x^4/120-x^6/5040 ✓)")

# Αριθμητικό πλέγμα — np.where για να αποφύγουμε τη διαίρεση 0/0.
xs   = np.linspace(-2 * np.pi, 2 * np.pi, 801)
safe = np.where(np.abs(xs) < 1e-12, 1.0, xs)          # ποτέ 0 στον παρονομαστή
ys   = np.where(np.abs(xs) < 1e-12, 1.0, np.sin(safe) / safe)

fig, axs = plt.subplots(1, 2, figsize=(12, 4.6))

axs[0].plot(xs, ys, 'k-', lw=2.4, label=r'$\sin(x)/x$')
colors = ['tab:blue', 'tab:orange', 'tab:green', 'tab:red']
errs = {}
for n, c in zip(orders, colors):
    p = lambdify(x, polys[n], 'numpy')
    # Το T1 είναι η σταθερά 1: το lambdify επιστρέφει βαθμωτό, οπότε το
    # «απλώνουμε» σε πίνακα ίδιου σχήματος με το xs.
    yp = np.asarray(p(xs), dtype=float) * np.ones_like(xs)
    axs[0].plot(xs, yp, '--', lw=1.6, color=c, label=f'Taylor τάξης {n}')
    errs[n] = np.abs(yp - ys)
axs[0].set_ylim(-1.5, 2.0)
axs[0].axhline(0, color='k', lw=.5)
axs[0].set_xlabel('x'); axs[0].set_ylabel('y')
axs[0].set_title(r'$\sin(x)/x$ και τα πολυώνυμα Taylor', fontsize=11)
axs[0].grid(alpha=.3); axs[0].legend(fontsize=8)

for n, c in zip(orders, colors):
    axs[1].semilogy(xs, np.maximum(errs[n], 1e-18), lw=1.5, color=c,
                    label=f'|σφάλμα| τάξης {n}')
axs[1].set_xlabel('x'); axs[1].set_ylabel('|σφάλμα| (λογαριθμική κλίμακα)')
axs[1].set_title('Σφάλμα προσέγγισης στο $[-2\\pi,\\,2\\pi]$', fontsize=11)
axs[1].grid(alpha=.3, which='both'); axs[1].legend(fontsize=8)
fig.tight_layout()

print("\n  Μέγιστο |σφάλμα| στο [-2π, 2π]:")
for n in orders:
    print(f"    τάξη {n}: {errs[n].max():.6f}")
print("  Μέγιστο |σφάλμα| στο μικρότερο διάστημα [-π/2, π/2]:")
mask = np.abs(xs) <= np.pi / 2
for n in orders:
    print(f"    τάξη {n}: {errs[n][mask].max():.8f}")
print("  -> Κοντά στο 0 το σφάλμα μειώνεται ΔΡΑΜΑΤΙΚΑ με την τάξη· μακριά")
print("  από το 0 (κοντά στο ±2π) τα πολυώνυμα αποκλίνουν από τη συνάρτηση.")

plt.show()
print("\n✓ Ολοκληρώθηκε.")
