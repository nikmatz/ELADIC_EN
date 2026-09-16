# ============================================================
# python_matrices.py
# Κεφάλαιο 2 — Πίνακες, NumPy, Αποσύνθεση LU, Heatmaps
# Ματζάκος, Ν. (2026). Στοιχεία Γραμμικής Άλγεβρας, Διαφορικού & Ολοκληρωτικού Λογισμού. NewTech Publications.
# ============================================================
#
# ΒΙΒΛΙΟΘΗΚΕΣ:
#   numpy         → αριθμητικές πράξεις πινάκων
#   scipy.linalg  → αποσύνθεση LU
#   sympy         → ακριβείς υπολογισμοί (κλάσματα)
#   matplotlib    → οπτικοποίηση (heatmaps πινάκων)
#
# ΒΑΣΙΚΕΣ ΕΝΤΟΛΕΣ:
#   A @ B                  → γινόμενο πινάκων
#   A.T                    → ανάστροφος
#   np.linalg.det(A)       → ορίζουσα
#   np.linalg.inv(A)       → αντίστροφος
#   np.linalg.solve(A, b)  → λύση A·x = b
#   scipy.linalg.lu(A)     → αποσύνθεση A = P·L·U
#   np.linalg.eigh(S)      → ιδιοτιμές συμμετρικού πίνακα
#
# Δραστηριότητα βιβλίου: (α) πράξεις NumPy, (β) επίλυση A·x = b,
#   (γ) A = P·L·U, (δ) θετική οριστικότητα του S, (ε) heatmaps.
# ============================================================

import numpy as np
import scipy.linalg as la
import matplotlib.pyplot as plt
import matplotlib.colors as mcolors
from sympy import Matrix, pprint

print("=" * 58)
print(" Κεφάλαιο 2: Πίνακες, LU, Heatmaps — Python")
print("=" * 58)

# Δεδομένα της δραστηριότητας Maxima (ίδια A, B, b)
A = np.array([[1, 2, 3],
              [0, 1, 4],
              [5, 6, 0]], dtype=float)

B = np.array([[2, -1, 0],
              [1,  3, 1],
              [0,  2, 4]], dtype=float)

b = np.array([1.0, 2.0, 3.0])

print("\nA =\n", A)
print("\nB =\n", B)
print("\nb =", b)

# ── Α. (α) Πράξεις με NumPy — σύγκριση με Maxima ──────────
print("\n── Α. (α) Πράξεις με NumPy ──")

AB = A @ B
BA = B @ A

print("A @ B =\n", AB)
print("  [Maxima: matrix([4,11,14],[1,11,17],[16,13,6])] →",
      np.allclose(AB, [[4, 11, 14], [1, 11, 17], [16, 13, 6]]))
print("\nB @ A =\n", BA)
print("A@B == B@A ;  Έλεγχος:", np.allclose(AB, BA))
print("  → False: ο πολλαπλασιασμός πινάκων δεν είναι αντιμεταθετικός")

print("\nAᵀ =\n", A.T)
print("(A@B)ᵀ == Bᵀ@Aᵀ ;  Έλεγχος:", np.allclose(AB.T, B.T @ A.T))

det_A = np.linalg.det(A)
det_B = np.linalg.det(B)
det_AB = np.linalg.det(AB)
print(f"\ndet(A)  = {det_A:.10f}   [Maxima: 1]")
print(f"det(B)  = {det_B:.10f}   [Maxima: 24]")
print(f"det(AB) = {det_AB:.10f}   [Maxima: 24]")
print("det(A·B) == det(A)·det(B) ;  Έλεγχος:",
      np.isclose(det_AB, det_A * det_B))

A_inv = np.linalg.inv(A)
print("\nA⁻¹ =\n", np.round(A_inv, 10))
print("  [Maxima: matrix([-24,18,5],[20,-15,-4],[-5,4,1])] →",
      np.allclose(A_inv, [[-24, 18, 5], [20, -15, -4], [-5, 4, 1]]))
print("A @ A⁻¹ =\n", np.round(A @ A_inv, 10))
print("A·A⁻¹ == I₃ ;  Έλεγχος:", np.allclose(A @ A_inv, np.eye(3)))

# Ακριβής (ρητός) υπολογισμός με SymPy — σύγκριση με το Maxima
A_sym = Matrix([[1, 2, 3], [0, 1, 4], [5, 6, 0]])
print("\nΑκριβής A⁻¹ (SymPy):")
pprint(A_sym.inv())

# ── Β. (β) Επίλυση A·x = b ────────────────────────────────
print("\n── Β. (β) Επίλυση A·x = b ──")

x = np.linalg.solve(A, b)
print("x = np.linalg.solve(A, b) =", np.round(x, 10))
print("  [Αναμένεται: (27, -22, 6)] →", np.allclose(x, [27, -22, 6]))
print("A @ x =", np.round(A @ x, 10))
print("A·x == b ;  Έλεγχος:", np.allclose(A @ x, b))
print(f"Υπόλοιπο ‖A·x - b‖ = {np.linalg.norm(A @ x - b):.2e}")

# Ακριβής λύση με SymPy
print("\nx (SymPy, ακριβής):",
      list(A_sym.solve(Matrix([1, 2, 3]))))

# ── Γ. (γ) Αποσύνθεση A = P·L·U ───────────────────────────
print("\n── Γ. (γ) Αποσύνθεση LU ──")

P, L, U = la.lu(A)

print("P (πίνακας μετάθεσης) =\n", P)
print("\nL (κάτω τριγωνικός, μονάδες στη διαγώνιο) =\n", np.round(L, 6))
print("\nU (άνω τριγωνικός) =\n", np.round(U, 6))
print("\nP @ L @ U =\n", np.round(P @ L @ U, 10))
print("P·L·U == A ;  Έλεγχος:", np.allclose(P @ L @ U, A))
print("L κάτω τριγωνικός:", np.allclose(L, np.tril(L)),
      "| U άνω τριγωνικός:", np.allclose(U, np.triu(U)))
print(f"det(A) = ±det(U) = {np.linalg.det(P) * np.prod(np.diag(U)):.10f}",
      "  Έλεγχος:",
      np.isclose(np.linalg.det(P) * np.prod(np.diag(U)), det_A))

# ── Δ. (δ) Συμμετρικός S: ιδιοτιμές & θετική οριστικότητα ─
print("\n── Δ. (δ) Συμμετρικός S — np.linalg.eigh ──")

S = np.array([[4, 2, 1],
              [2, 5, 3],
              [1, 3, 6]], dtype=float)

print("S =\n", S)
print("S == Sᵀ ;  Έλεγχος:", np.allclose(S, S.T))

eigvals, eigvecs = np.linalg.eigh(S)     # eigh: συμμετρικός → πραγματικές λ
print("\nΙδιοτιμές (eigh):", np.round(eigvals, 6))
print("Ιδιοδιανύσματα (στήλες Q):\n", np.round(eigvecs, 6))
print("QᵀQ == I ;  Έλεγχος:", np.allclose(eigvecs.T @ eigvecs, np.eye(3)))
print("QΛQᵀ == S ;  Έλεγχος:",
      np.allclose(eigvecs @ np.diag(eigvals) @ eigvecs.T, S))

# Κριτήριο 1: όλες οι ιδιοτιμές > 0
pd_eig = bool(np.all(eigvals > 0))
# Κριτήριο 2 (Sylvester): όλα τα ηγετικά κύρια ελάσσονα > 0
minors = [float(np.linalg.det(S[:k, :k])) for k in (1, 2, 3)]
pd_minors = all(m > 0 for m in minors)
# Κριτήριο 3: υπάρχει ανάλυση Cholesky
try:
    np.linalg.cholesky(S)
    pd_chol = True
except np.linalg.LinAlgError:
    pd_chol = False

print(f"\nΗγετικά κύρια ελάσσονα: {[round(m, 6) for m in minors]}"
      "   [Αναμένονται 4, 16, 67]")
print(f"Κριτήριο ιδιοτιμών  (όλες λᵢ > 0): {pd_eig}")
print(f"Κριτήριο Sylvester  (ελάσσονα > 0): {pd_minors}")
print(f"Κριτήριο Cholesky   (υπάρχει L):    {pd_chol}")
print("→ Ο S είναι θετικά ορισμένος:",
      pd_eig and pd_minors and pd_chol)
print("ΠΡΟΣΟΧΗ: το det(S) > 0 ΜΟΝΟ του δεν αρκεί "
      "(π.χ. ο -I₂ έχει det = 1 > 0 αλλά είναι αρνητικά ορισμένος).")

# Έλεγχος με τυχαία διανύσματα: xᵀSx > 0 για κάθε x ≠ 0
rng = np.random.default_rng(0)
X = rng.normal(size=(3, 200))
qvals = np.sum(X * (S @ X), axis=0)
print(f"min(xᵀSx) σε 200 τυχαία x: {qvals.min():.6f} > 0 →",
      bool(qvals.min() > 0))

# ── Ε. (ε) Προαιρετικό: Heatmaps των A, A·B και L ─────────
print("\n── Ε. (ε) Heatmaps (προαιρετικό) ──")

fig, axes = plt.subplots(1, 3, figsize=(13, 4))
fig.suptitle("Κεφ. 2 — Heatmaps πινάκων", fontsize=13, fontweight='bold')


def plot_matrix(ax, M, title, fmt=".1f"):
    """Εμφάνιση πίνακα ως heatmap με τις αριθμητικές τιμές."""
    vmax = max(abs(M.min()), abs(M.max()), 1e-9)
    im = ax.imshow(M, cmap='RdBu_r', aspect='auto',
                   norm=mcolors.TwoSlopeNorm(vcenter=0,
                                             vmin=-vmax, vmax=vmax))
    ax.set_title(title, fontsize=10)
    for i in range(M.shape[0]):
        for j in range(M.shape[1]):
            ax.text(j, i, format(M[i, j], fmt),
                    ha='center', va='center', fontsize=9,
                    color='black' if abs(M[i, j]) < 0.7 * vmax else 'white')
    ax.set_xticks([]); ax.set_yticks([])
    plt.colorbar(im, ax=ax, shrink=0.8)


plot_matrix(axes[0], A,  "Πίνακας A")
plot_matrix(axes[1], AB, "A · B")
plot_matrix(axes[2], L,  "L (από την A = P·L·U)")

plt.tight_layout()
print("Δημιουργήθηκε heatmap για A, A·B και L.")
plt.show()
