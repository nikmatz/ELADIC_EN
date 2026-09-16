# ============================================================
# python_eigen.py
# Κεφάλαιο 5 — Ιδιοτιμές, NumPy, Ιδιόχωροι, Markov
# Ματζάκος, Ν. (2026). Στοιχεία Γραμμικής Άλγεβρας, Διαφορικού & Ολοκληρωτικού Λογισμού. NewTech Publications.
# ============================================================
#
# ΒΙΒΛΙΟΘΗΚΕΣ:
#   numpy         → αριθμητικές ιδιοτιμές (eig), δυνάμεις πινάκων
#   sympy         → ακριβείς ιδιοτιμές, ιδιόχωροι, χαρ. πολυώνυμο
#   matplotlib    → σύγκλιση power iteration & αλυσίδας Markov
#
# ΒΑΣΙΚΕΣ ΕΝΤΟΛΕΣ:
#   sympy.Matrix.eigenvects()  → (λ, m_a, [ιδιοδιανύσματα]) ακριβώς
#   sympy.Matrix.charpoly()    → χαρακτηριστικό πολυώνυμο
#   np.linalg.eig(A)           → ιδιοτιμές + ιδιοδιανύσματα (αριθμητικά)
#   np.linalg.matrix_power(M,n)→ Mⁿ
#   np.diag(v)                 → διαγώνιος πίνακας
#
# Δραστηριότητα βιβλίου: (α) ακριβείς ιδιοτιμές/ιδιοδιανύσματα του A,
#   (β) αριθμητική επαλήθευση A·v = λ·v, (γ) ελαττωματικός πίνακας
#   [[3,1],[0,3]], (δ) στάσιμη κατανομή Markov, (ε) γραφήματα.
# ============================================================

import numpy as np
import matplotlib.pyplot as plt
from sympy import Matrix, Symbol, Rational, factor

print("=" * 58)
print(" Κεφάλαιο 5: Ιδιοτιμές & Ιδιόχωροι — Python")
print("=" * 58)

# ── Α. (α) Ακριβείς ιδιοτιμές/ιδιοδιανύσματα με SymPy ─────
print("\n── Α. (α) SymPy: eigenvects, trace, det ──")

A_sym = Matrix([[4, 1],
                [2, 3]])
lam = Symbol('lambda')

print("A =", A_sym.tolist())
print("p(λ) = det(A - λI) =", factor(A_sym.charpoly(lam).as_expr()))
print("  [Αναμένεται: (λ-5)(λ-2) ✓]")

print("\neigenvects(A):")
eig_list = []          # λίστα ιδιοτιμών ΜΕ τις πολλαπλότητές τους
for eigval, m_a, vecs in A_sym.eigenvects():
    eig_list.extend([eigval] * m_a)
    print(f"  λ = {eigval}   (αλγεβρική πολλαπλότητα m_a = {m_a},"
          f" γεωμετρική m_g = {len(vecs)})")
    for v in vecs:
        print("    ιδιοδιάνυσμα vᵀ =", list(v))
        print("    A·v = λ·v ;  Έλεγχος:", (A_sym * v) == (eigval * v))

tr_A, det_A = A_sym.trace(), A_sym.det()
sum_l = sum(eig_list)             # άθροισμα ΜΕ τις πολλαπλότητες
prod_l = 1
for e in eig_list:
    prod_l *= e

print(f"\ntr(A) = {tr_A} | Σλᵢ = {sum_l} | Ισότητα: {tr_A == sum_l}")
print(f"det(A) = {det_A} | Πλᵢ = {prod_l} | Ισότητα: {det_A == prod_l}")
print("  [Αναμένονται tr = 7 = 5+2, det = 10 = 5·2 ✓]")

# ── Β. (β) Αριθμητική επαλήθευση A·v = λ·v (NumPy) ────────
print("\n── Β. (β) NumPy: np.linalg.eig και A·v = λ·v ──")

A = np.array([[4, 1],
              [2, 3]], dtype=float)

vals, vecs = np.linalg.eig(A)
print("Ιδιοτιμές:", np.round(vals, 10))

all_ok = True
for i in range(len(vals)):
    lv, v = vals[i], vecs[:, i]
    res = A @ v - lv * v
    ok = bool(np.allclose(res, 0))
    all_ok = all_ok and ok
    print(f"  λ{i+1} = {lv:.6f}  v{i+1} = {np.round(v, 6)}")
    print(f"    A·v = {np.round(A @ v, 6)}   λ·v = {np.round(lv * v, 6)}")
    print(f"    ‖A·v - λ·v‖ = {np.linalg.norm(res):.2e}  →  {ok}")
print("Όλες οι σχέσεις A·v = λ·v επαληθεύονται:", all_ok)

# Διαγωνοποίηση: A = P·D·P⁻¹ (χρήσιμη στο (ε))
P = vecs
D = np.diag(vals)
print("P·D·P⁻¹ == A ;  Έλεγχος:",
      bool(np.allclose(P @ D @ np.linalg.inv(P), A)))

# ── Γ. (γ) Ελαττωματικός πίνακας [[3,1],[0,3]] ────────────
print("\n── Γ. (γ) Ελαττωματική ιδιοτιμή: B = [[3,1],[0,3]] ──")

B_sym = Matrix([[3, 1],
                [0, 3]])
print("B =", B_sym.tolist())
print("p(λ) =", factor(B_sym.charpoly(lam).as_expr()),
      "  [Αναμένεται: (λ-3)² ✓]")
print("eigenvals(B) =", B_sym.eigenvals(), "  → λ = 3 με m_a = 2")

for eigval, m_a, vecs_b in B_sym.eigenvects():
    m_g = len(vecs_b)
    print(f"\n  λ = {eigval}")
    print(f"  αλγεβρική πολλαπλότητα  m_a = {m_a}")
    print(f"  ιδιόχωρος ker(B - λI) = span{[list(v) for v in vecs_b]}")
    print(f"  γεωμετρική πολλαπλότητα m_g = dim ker = {m_g}")
    print(f"  m_g < m_a ;  Έλεγχος: {m_g < m_a}"
          f"  ({m_g} < {m_a})")
    if m_g < m_a:
        print("  → Η ιδιοτιμή είναι ΕΛΑΤΤΩΜΑΤΙΚΗ (defective)")

# Ο ιδιόχωρος και μέσω nullspace του B - 3I
N = (B_sym - 3 * Matrix.eye(2)).nullspace()
print("\nnullspace(B - 3I) =", [list(v) for v in N],
      " | διάσταση =", len(N))
print("rank(B - 3I) =", (B_sym - 3 * Matrix.eye(2)).rank(),
      " → dim ker = 2 - rank =", 2 - (B_sym - 3 * Matrix.eye(2)).rank())
print("Ο B είναι διαγωνοποιήσιμος:", B_sym.is_diagonalizable(),
      " (χρειάζονταν 2 γραμμικά ανεξάρτητα ιδιοδιανύσματα, υπάρχει 1)")

# ── Δ. (δ) Αλυσίδα Markov: στάσιμη κατανομή ───────────────
print("\n── Δ. (δ) Αλυσίδα Markov — στάσιμη κατανομή π ──")

M = np.array([[0.8, 0.3],
              [0.2, 0.7]])
print("M =\n", M)
print("Στοχαστικός κατά στήλες (άθροισμα στηλών = 1):",
      bool(np.allclose(M.sum(axis=0), 1.0)))

M_vals, M_vecs = np.linalg.eig(M)
print("Ιδιοτιμές M:", np.round(M_vals, 10),
      " → υπάρχει λ = 1:", bool(np.any(np.isclose(M_vals, 1.0))))

idx = int(np.argmin(np.abs(M_vals - 1.0)))
pi = M_vecs[:, idx].real
pi = pi / pi.sum()                     # κανονικοποίηση σε κατανομή
print("π =", np.round(pi, 10), "  [Αναμένεται (0.6, 0.4)]")
print("Άθροισμα π = ", round(float(pi.sum()), 10))
print("M·π =", np.round(M @ pi, 10))
print("M·π == π ;  Έλεγχος:", bool(np.allclose(M @ pi, pi)))

# Ακριβής υπολογισμός με SymPy (ρητοί αριθμοί)
M_sym = Matrix([[Rational(8, 10), Rational(3, 10)],
                [Rational(2, 10), Rational(7, 10)]])
ns = (M_sym - Matrix.eye(2)).nullspace()[0]
pi_exact = ns / sum(ns)
print("π (ακριβώς, SymPy) =", list(pi_exact), "  [= (3/5, 2/5) ✓]")
print("M·π = π (ακριβώς) ;  Έλεγχος:", (M_sym * pi_exact) == pi_exact)

# Σύγκλιση Mⁿ → [π | π]
M50 = np.linalg.matrix_power(M, 50)
print("\nM⁵⁰ =\n", np.round(M50, 10))
print("Κάθε στήλη του M⁵⁰ ισούται με π ;  Έλεγχος:",
      bool(np.allclose(M50, np.column_stack([pi, pi]))))

# ── Ε. (ε) Προαιρετικό: power iteration & Markov (γραφικά) ─
print("\n── Ε. (ε) Προαιρετικό: γραφήματα σύγκλισης ──")


def power_iteration(Mat, num_iter=25, seed=42):
    """Μέθοδος δύναμης: εκτίμηση της κυρίαρχης ιδιοτιμής (πηλίκο Rayleigh)."""
    rng = np.random.default_rng(seed)
    x = rng.normal(size=Mat.shape[0])
    x = x / np.linalg.norm(x)
    estimates = []
    for _ in range(num_iter):
        y = Mat @ x
        x = y / np.linalg.norm(y)
        estimates.append(float(x @ (Mat @ x)))   # πηλίκο Rayleigh
    return x, estimates


v_est, history = power_iteration(A)
lam_max = float(np.max(vals))
lam_est = history[-1]
print(f"Κυρίαρχη ιδιοτιμή (power iteration, 25 βήματα): {lam_est:.10f}")
print(f"Ακριβής τιμή λ_max = {lam_max:.10f}"
      f"  | σφάλμα = {abs(lam_est - lam_max):.2e}"
      f"  | σύγκλιση: {abs(lam_est - lam_max) < 1e-8}")

# Πορεία της αλυσίδας Markov από την κατάσταση (1, 0)
state = np.array([1.0, 0.0])
traj = [state.copy()]
for _ in range(25):
    state = M @ state
    traj.append(state.copy())
traj = np.array(traj)
print(f"Κατάσταση μετά από 25 βήματα: {np.round(traj[-1], 8)}"
      f"  | ταυτίζεται με π: {bool(np.allclose(traj[-1], pi))}")

fig, axes = plt.subplots(1, 3, figsize=(14, 4.5))
fig.suptitle("Κεφ. 5 — Ιδιοδιανύσματα, Power Iteration, Markov",
             fontsize=13, fontweight='bold')

# (1) Ιδιοδιανύσματα του A στο επίπεδο
ax1 = axes[0]
ax1.set_title("Ιδιοδιανύσματα του $A$")
colors = ['royalblue', 'tomato']
for i in range(2):
    vn = vecs[:, i] / np.linalg.norm(vecs[:, i])
    ax1.annotate('', xy=vn, xytext=(0, 0),
                 arrowprops=dict(arrowstyle='->', color=colors[i], lw=2.5))
    ax1.annotate(f'$v_{i+1}$, $\\lambda={vals[i]:.0f}$', vn,
                 fontsize=9, color=colors[i],
                 xytext=(6, 6), textcoords='offset points')
ax1.set_xlim(-1.5, 1.5); ax1.set_ylim(-1.5, 1.5)
ax1.axhline(0, color='k', lw=0.5); ax1.axvline(0, color='k', lw=0.5)
ax1.grid(True, alpha=0.3); ax1.set_aspect('equal')
ax1.set_xlabel('x'); ax1.set_ylabel('y')

# (2) Σύγκλιση power iteration
ax2 = axes[1]
ax2.set_title("Σύγκλιση Power Iteration")
ax2.plot(range(1, len(history) + 1), history, 'o-', color='royalblue',
         lw=1.8, ms=3, label='πηλίκο Rayleigh')
ax2.axhline(lam_max, color='tomato', ls='--', lw=1.5,
            label=f'$\\lambda_{{max}}={lam_max:.0f}$')
ax2.set_xlabel("Επανάληψη"); ax2.set_ylabel("Εκτίμηση $\\lambda$")
ax2.legend(fontsize=9); ax2.grid(True, alpha=0.3)

# (3) Σύγκλιση αλυσίδας Markov προς π
ax3 = axes[2]
ax3.set_title("Αλυσίδα Markov → στάσιμη $\\pi$")
ax3.plot(traj[:, 0], color='royalblue', lw=2, label='Κατάσταση 1')
ax3.plot(traj[:, 1], color='tomato', lw=2, label='Κατάσταση 2')
ax3.axhline(pi[0], color='royalblue', ls='--', lw=1, alpha=0.7)
ax3.axhline(pi[1], color='tomato', ls='--', lw=1, alpha=0.7)
ax3.text(14, pi[0] + 0.03, f'$\\pi_1={pi[0]:.1f}$', color='royalblue',
         fontsize=9)
ax3.text(14, pi[1] - 0.07, f'$\\pi_2={pi[1]:.1f}$', color='tomato',
         fontsize=9)
ax3.set_xlabel("Βήματα"); ax3.set_ylabel("Πιθανότητα")
ax3.set_ylim(0, 1.05)
ax3.legend(fontsize=9); ax3.grid(True, alpha=0.3)

plt.tight_layout()
print("Δημιουργήθηκαν τα γραφήματα σύγκλισης.")
plt.show()
