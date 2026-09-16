# ============================================================
# python_synartiseis.py
# Κεφάλαιο 8 — Συναρτήσεις, SymPy & Matplotlib
# Ματζάκος, Ν. (2026). Στοιχεία Γραμμικής Άλγεβρας, Διαφορικού & Ολοκληρωτικού Λογισμού. NewTech Publications.
# ============================================================
#
# ΒΙΒΛΙΟΘΗΚΕΣ:
#   sympy      -> συμβολικοί υπολογισμοί (πεδίο ορισμού, αντίστροφη)
#   numpy      -> αριθμητική αποτίμηση για τα γραφήματα
#   matplotlib -> γραφικές παραστάσεις
#
# ΒΑΣΙΚΕΣ ΕΝΤΟΛΕΣ:
#   sympy.calculus.util.continuous_domain(expr, x, S.Reals) -> ΠΕΔΙΟ ΟΡΙΣΜΟΥ
#   sympy.solveset(expr, x, domain=S.Reals)                 -> ΡΙΖΕΣ (όχι πεδίο!)
#   sympy.solve(Eq(y, f), x)   -> αντίστροφη συνάρτηση
#   sympy.lambdify(x, expr)    -> μετατροπή σε αριθμητική f(x)
#   sympy.Piecewise(...)       -> τμηματικά ορισμένη συνάρτηση
#   sympy.simplify(...)        -> απλοποίηση (έλεγχος αρτιότητας)
#   np.linspace(), matplotlib.pyplot
# ============================================================

import numpy as np
import matplotlib.pyplot as plt
import sympy as sp
from sympy import symbols, sqrt, log, exp, Eq, S, simplify, solve, solveset, lambdify
from sympy.calculus.util import continuous_domain

x, y = symbols('x y', real=True)

print("=" * 62)
print(" Κεφάλαιο 8: Συναρτήσεις — SymPy & Matplotlib")
print("=" * 62)


# ── Α. (α) Πεδίο ορισμού με continuous_domain ────────────────
def domain(expr, var=x):
    """Επιστρέφει το ΠΕΔΙΟ ΟΡΙΣΜΟΥ της expr στο R.

    ΠΡΟΣΟΧΗ: το solveset(expr, x) δίνει τις ΡΙΖΕΣ (πού μηδενίζεται η
    συνάρτηση) και ΟΧΙ το πεδίο ορισμού. Για το πεδίο ορισμού
    χρησιμοποιούμε την continuous_domain.
    """
    return continuous_domain(expr, var, S.Reals)


print("\n[Α] Πεδίο ορισμού — domain(expr) με continuous_domain")

funcs_a = [
    ("sqrt(x-2)/(x^2-9)", sqrt(x - 2) / (x**2 - 9), "[2,3) ∪ (3,+∞)"),
    ("ln(4-x^2)",         log(4 - x**2),            "(-2,2)"),
    ("1/sqrt(1-x^2)",     1 / sqrt(1 - x**2),       "(-1,1)"),
]
for name, expr, expected in funcs_a:
    print(f"  {name:20s} -> {domain(expr)}")
    print(f"  {'':20s}    αναμενόμενο (και από το Maxima): {expected} ✓")

# Αντιπαράδειγμα: τι ΔΙΝΕΙ πράγματι το solveset — τις ρίζες.
print("\n  Σύγκριση για τη sqrt(x-2)/(x^2-9):")
print("    ρίζες  solveset(expr, x, S.Reals) =",
      solveset(sqrt(x - 2) / (x**2 - 9), x, domain=S.Reals), " (= {2} ✓)")
print("    πεδίο  continuous_domain(...)     =",
      domain(sqrt(x - 2) / (x**2 - 9)))
print("    -> τα δύο σύνολα είναι ΔΙΑΦΟΡΕΤΙΚΑ πράγματα.")

# Αριθμητικός έλεγχος τιμών και άκρων.
fa = sqrt(x - 2) / (x**2 - 9)
print("  Έλεγχος τιμών: f(2) =", fa.subs(x, 2), " (= 0 ✓)")
print("                 f(6) =", fa.subs(x, 6), "=", float(fa.subs(x, 6)),
      " (= 2/27 = 0,0740741 ✓)")
print("                 2 ∈ πεδίο;", domain(fa).contains(2), " (True ✓)")
print("                 3 ∈ πεδίο;", domain(fa).contains(3),
      " (False ✓ — μηδενίζεται ο παρονομαστής)")
print("                 1 ∈ πεδίο;", domain(fa).contains(1),
      " (False ✓ — αρνητικό υπόρριζο)")

# ── Β. (β) Αρτιότητα / περιττότητα, προγραμματιστικά ─────────
print("\n[Β] Αρτιότητα / περιττότητα με simplify(f(-x) ∓ f(x))")

funcs_b = [
    ("x^4 - 3x^2",   x**4 - 3 * x**2,   "ΑΡΤΙΑ"),
    ("x^3 - x",      x**3 - x,          "ΠΕΡΙΤΤΗ"),
    ("e^x + e^(-x)", exp(x) + exp(-x),  "ΑΡΤΙΑ"),
    ("x^2 + x",      x**2 + x,          "ΟΥΤΕ"),
]


def parity(expr, var=x):
    """Το συμπέρασμα προκύπτει από τον έλεγχο, δεν είναι σταθερό κείμενο."""
    if simplify(expr.subs(var, -var) - expr) == 0:
        return "ΑΡΤΙΑ"
    if simplify(expr.subs(var, -var) + expr) == 0:
        return "ΠΕΡΙΤΤΗ"
    return "ΟΥΤΕ"


for name, expr, expected in funcs_b:
    d = simplify(expr.subs(x, -x) - expr)
    s = simplify(expr.subs(x, -x) + expr)
    got  = parity(expr)
    mark = "✓" if got == expected else "✗"
    print(f"  {name:14s} f(-x)-f(x) = {str(d):18s} f(-x)+f(x) = {str(s):22s}"
          f" -> {got}  (αναμενόμενο: {expected} {mark})")

fig1, axs1 = plt.subplots(2, 2, figsize=(9, 6))
xs_b = np.linspace(-2, 2, 400)
for axi, (name, expr, _) in zip(axs1.ravel(), funcs_b):
    fnum = lambdify(x, expr, 'numpy')
    axi.plot(xs_b, fnum(xs_b), lw=2, color='tab:blue')
    axi.axhline(0, color='k', lw=.6)
    axi.axvline(0, color='k', lw=.6)
    axi.set_title(f"{name}  —  {parity(expr)}", fontsize=10)
    axi.grid(alpha=.3)
fig1.suptitle("Άρτια: συμμετρία ως προς τον άξονα y · Περιττή: ως προς την αρχή",
              fontsize=10)
fig1.tight_layout()

# ── Γ. (γ) Η f(x)=(2x+1)/(x-3): 1-1 και αντίστροφη ───────────
print("\n[Γ] Η f(x) = (2x+1)/(x-3): 1-1 και αντίστροφη")

f_expr = (2 * x + 1) / (x - 3)
print("  f(x) =", f_expr, "  (πεδίο ορισμού: R \\ {3})")
print("  f'(x) =", sp.simplify(sp.diff(f_expr, x)),
      " = -7/(x-3)^2 < 0 -> γνησίως φθίνουσα σε κάθε κλάδο, άρα 1-1 ✓")

sol = solve(Eq(y, f_expr), x)
print("  solve(Eq(y, f), x) =", sol, " (= [(3y+1)/(y-2)] ✓)")

finv_expr = sol[0].subs(y, x)
print("  f^(-1)(x) =", finv_expr, "  (= (3x+1)/(x-2) ✓)")
print("  Επαλήθευση f(f^(-1)(x)) =", simplify(f_expr.subs(x, finv_expr)), " (= x ✓)")
print("  Επαλήθευση f^(-1)(f(x)) =", simplify(finv_expr.subs(x, f_expr)), " (= x ✓)")
print("  Αριθμητικά: f(5) =", f_expr.subs(x, 5), "(= 11/2) και f^(-1)(11/2) =",
      finv_expr.subs(x, sp.Rational(11, 2)), "(= 5 ✓)")

f_num    = lambdify(x, f_expr, 'numpy')
finv_num = lambdify(x, finv_expr, 'numpy')


def masked(fn, xs, pole, eps=0.15):
    """Αποκόπτει τιμές κοντά στην κατακόρυφη ασύμπτωτο (αποφυγή 1/0)."""
    xs = xs[np.abs(xs - pole) > eps]
    return xs, fn(xs)


fig2, ax2 = plt.subplots(figsize=(6.2, 6.2))
for lo, hi, pole in [(-8, 3, 3), (3, 12, 3)]:
    xs, ys = masked(f_num, np.linspace(lo, hi, 600), pole)
    ax2.plot(xs, ys, color='tab:blue', lw=2,
             label='$f(x)=\\frac{2x+1}{x-3}$' if lo < 0 else None)
for lo, hi, pole in [(-8, 2, 2), (2, 12, 2)]:
    xs, ys = masked(finv_num, np.linspace(lo, hi, 600), pole)
    ax2.plot(xs, ys, color='tab:red', lw=2,
             label='$f^{-1}(x)=\\frac{3x+1}{x-2}$' if lo < 0 else None)
xs_line = np.linspace(-8, 12, 200)
ax2.plot(xs_line, xs_line, 'k--', lw=1, label='$y = x$')
ax2.axhline(2, color='tab:blue', ls=':', lw=.9)   # οριζόντια ασύμπτωτος της f
ax2.axvline(3, color='tab:blue', ls=':', lw=.9)   # κατακόρυφη ασύμπτωτος της f
ax2.axhline(3, color='tab:red', ls=':', lw=.9)    # οριζόντια ασύμπτωτος της f^-1
ax2.axvline(2, color='tab:red', ls=':', lw=.9)    # κατακόρυφη ασύμπτωτος της f^-1
ax2.set_xlim(-8, 12); ax2.set_ylim(-8, 12)
ax2.set_aspect('equal')          # ΑΠΑΡΑΙΤΗΤΟ για να φανεί η συμμετρία
ax2.grid(alpha=.3); ax2.legend(loc='lower right', fontsize=9)
ax2.set_title("$f$, $f^{-1}$ και η $y=x$: κατοπτρική συμμετρία", fontsize=11)
fig2.tight_layout()
print("  Στο γράφημα: η x=3 (ασύμπτωτος της f) γίνεται y=3 για την f^(-1).")

# ── Δ. (δ) Μετασχηματισμοί a·f(b(x-c))+d και τμηματική p ─────
print("\n[Δ] Μετασχηματισμοί a·f(b(x-c))+d της f(x)=x^2")

base = x**2
params = [
    (1, 1, 2, 0, "f(x-2): μετατόπιση 2 ΔΕΞΙΑ"),
    (1, 1, 0, 3, "f(x)+3: μετατόπιση 3 ΠΑΝΩ"),
    (2, 1, 0, 0, "2f(x): κατακόρυφη επιμήκυνση ×2"),
    (1, 2, 0, 0, "f(2x): οριζόντια συστολή ×1/2"),
]
xs_d = np.linspace(-4, 5, 500)
base_num = lambdify(x, base, 'numpy')

fig3, axs3 = plt.subplots(2, 2, figsize=(9.5, 6.5))
for axi, (a, b, c, d, descr) in zip(axs3.ravel(), params):
    expr = a * base.subs(x, b * (x - c)) + d
    print(f"  a={a}, b={b}, c={c}, d={d} -> {sp.expand(expr)}   [{descr}]")
    g_num = lambdify(x, sp.expand(expr), 'numpy')
    axi.plot(xs_d, base_num(xs_d), 'k--', lw=1.2, label='$f(x)=x^2$')
    axi.plot(xs_d, g_num(xs_d), lw=2, color='tab:red',
             label=f'$a f(b(x-c))+d$, $a$={a}, $b$={b}, $c$={c}, $d$={d}')
    axi.set_ylim(-2, 16); axi.grid(alpha=.3)
    axi.legend(fontsize=8, loc='upper center')
    axi.set_title(descr, fontsize=9)
# Η ανάκλαση -f(x) ζητείται επίσης από το βιβλίο:
refl = -base
print("  a=-1, b=1, c=0, d=0 ->", refl, "  [-f(x): ανάκλαση ως προς τον άξονα x]")
fig3.suptitle("Μετασχηματισμοί της $f(x)=x^2$", fontsize=11)
fig3.tight_layout()

fig3b, ax3b = plt.subplots(figsize=(6, 4))
ax3b.plot(xs_d, base_num(xs_d), 'k--', lw=1.2, label='$f(x)=x^2$')
ax3b.plot(xs_d, -base_num(xs_d), lw=2, color='tab:purple', label='$-f(x)$')
ax3b.axhline(0, color='k', lw=.6)
ax3b.set_ylim(-16, 16); ax3b.grid(alpha=.3); ax3b.legend(fontsize=9)
ax3b.set_title("Ανάκλαση ως προς τον άξονα $x$", fontsize=10)
fig3b.tight_layout()

# Τμηματική p(x) = x^2 για x<1,  2x-1 για x>=1
print("\n  Τμηματική p(x) = x^2 (x<1),  2x-1 (x>=1)  με sympy.Piecewise")
p = sp.Piecewise((x**2, x < 1), (2 * x - 1, x >= 1))
print("  p(x) =", p)
for v in (-1, 0, sp.Rational(1, 2), 1, sp.Rational(3, 2), 3):
    print(f"    p({v}) = {p.subs(x, v)}")

lm = sp.limit(p, x, 1, '-')
lp = sp.limit(p, x, 1, '+')
pa = p.subs(x, 1)
print("  lim x->1^- p(x) =", lm, " (= 1 ✓)")
print("  lim x->1^+ p(x) =", lp, " (= 1 ✓)")
print("  p(1) =", pa, " (= 1 ✓)")
print("  Συνεχής στο x=1;", bool(lm == lp == pa), " (True ✓)")

p_num = lambdify(x, p, 'numpy')
xs_p = np.linspace(-2, 3, 600)
fig4, ax4 = plt.subplots(figsize=(6.5, 4.2))
ax4.plot(xs_p, p_num(xs_p), lw=2, color='tab:green', label='$p(x)$')
ax4.plot([1], [float(pa)], 'o', color='tab:red', ms=9, zorder=5,
         label='$x=1$: $p(1)=1$, χωρίς άλμα')
ax4.axvline(1, color='k', ls=':', lw=.9)
ax4.grid(alpha=.3); ax4.legend(fontsize=9)
ax4.set_xlabel('x'); ax4.set_ylabel('p(x)')
ax4.set_title("Τμηματική $p$: συνεχής στο σημείο ραφής $x=1$", fontsize=10)
fig4.tight_layout()

plt.show()
print("\n✓ Ολοκληρώθηκε.")
