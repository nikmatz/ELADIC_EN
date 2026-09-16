# ============================================================
# python_diag.py
# Κεφάλαιο 6 — Διαγωνοποίηση, SVD, e^A, Τετραγωνικές Μορφές
# Ματζάκος, Ν. (2026). Στοιχεία Γραμμικής Άλγεβρας, Διαφορικού & Ολοκληρωτικού Λογισμού. NewTech Publications.
# ============================================================
#
# ΒΙΒΛΙΟΘΗΚΕΣ:
#   numpy         → eig, eigh, svd, matrix_power
#   scipy.linalg  → expm (εκθετική πίνακα)
#   sympy         → ακριβής έλεγχος διαγωνοποιησιμότητας
#   matplotlib    → ισοσταθμικές τετραγωνικής μορφής, SVD, στροφή
#
# ΒΑΣΙΚΕΣ ΕΝΤΟΛΕΣ:
#   np.linalg.eig(A)         → διαγωνοποίηση (γενική): A = P·D·P⁻¹
#   np.linalg.eigh(S)        → συμμετρικοί: ΟΡΘΟΚΑΝΟΝΙΚΑ ιδιοδιανύσματα
#   np.linalg.svd(M)         → SVD: M = U·Σ·Vᵀ
#   scipy.linalg.expm(A)     → εκθετική e^A
#   np.linalg.matrix_power   → Aⁿ άμεσα (για σύγκριση)
#   plt.contour(...)         → ισοσταθμικές καμπύλες
#
# Δραστηριότητα βιβλίου: (α) διαγωνοποίηση του A και A¹⁰,
#   (β) φασματικό θεώρημα για τον S, (γ) SVD & προσέγγιση rank-1,
#   (δ) e^(π/2·A₀) = R(π/2), (ε) ισοσταθμικές της xᵀSx.
# ============================================================

import numpy as np
import scipy.linalg as sla
import matplotlib.pyplot as plt
from sympy import Matrix, nsimplify

print("=" * 58)
print(" Κεφάλαιο 6: Διαγωνοποίηση, SVD, e^A — Python")
print("=" * 58)

# ── Α. (α) Διαγωνοποίηση A = P·D·P⁻¹ και A¹⁰ ──────────────
print("\n── Α. (α) Διαγωνοποίηση A = P·D·P⁻¹ ──")

A = np.array([[5, 4],
              [1, 2]], dtype=float)
print("A =\n", A)

vals, P = np.linalg.eig(A)
D = np.diag(vals)
P_inv = np.linalg.inv(P)

print("Ιδιοτιμές:", np.round(vals, 10), "  [Αναμένονται 6 και 1]")
print("P (στήλες = ιδιοδιανύσματα) =\n", np.round(P, 6))
print(f"det(P) = {np.linalg.det(P):.6f} ≠ 0 → ο P αντιστρέφεται:",
      bool(not np.isclose(np.linalg.det(P), 0)))
print("P·D·P⁻¹ =\n", np.round(P @ D @ P_inv, 10))
print("P·D·P⁻¹ == A ;  Έλεγχος:", bool(np.allclose(P @ D @ P_inv, A)))

n_pow = 10
A_pow_diag = P @ np.diag(vals ** n_pow) @ P_inv
A_pow_direct = np.linalg.matrix_power(A, n_pow)
print("\nA¹⁰ = P·D¹⁰·P⁻¹ =\n", np.round(A_pow_diag, 4))
print("A¹⁰ = np.linalg.matrix_power(A,10) =\n", A_pow_direct)
print("  [Αναμένεται: [[48372941, 48372940], [12093235, 12093236]]]")
print("Οι δύο υπολογισμοί συμπίπτουν ;  Έλεγχος:",
      bool(np.allclose(A_pow_diag, A_pow_direct)))
print("Ταυτίζονται με την αναμενόμενη τιμή:",
      bool(np.allclose(A_pow_direct,
                       [[48372941, 48372940], [12093235, 12093236]])))

# Συμπλήρωμα (αντιστοιχεί στο ερώτημα (β) της δραστηριότητας Maxima):
# γιατί ο B = [[3,1],[0,3]] ΔΕΝ διαγωνοποιείται.
print("\nΣυμπλήρωμα: έλεγχος διαγωνοποιησιμότητας")


def diagonalizability_report(M, name):
    """Συγκρίνει αλγεβρική και γεωμετρική πολλαπλότητα κάθε ιδιοτιμής.
    Διαγωνοποιήσιμος ⇔ Σ m_g = n (ΟΧΙ από την τάξη ενός μόνο M - λI).
    ΠΡΟΣΟΧΗ: ο έλεγχος γίνεται ΑΚΡΙΒΩΣ (nsimplify), γιατί με δεκαδικούς
    η SymPy «σπάει» μια διπλή ιδιοτιμή σε δύο απλές λόγω στρογγύλευσης."""
    Ms = Matrix(M.tolist()).applyfunc(nsimplify)
    n = M.shape[0]
    total_geo = 0
    for eigval, m_a, vecs in Ms.eigenvects():
        m_g = len(vecs)
        total_geo += m_g
        print(f"  {name}: λ = {eigval}  m_a = {m_a}  m_g = {m_g}"
              f"  {'(ελαττωματική)' if m_g < m_a else ''}")
    ok = (total_geo == n)
    print(f"  Σ m_g = {total_geo} (n = {n}) → διαγωνοποιήσιμος: {ok}")
    # Διασταύρωση με τον ελεγκτή της SymPy
    print(f"  SymPy is_diagonalizable(): {Ms.is_diagonalizable()}"
          f"  | συμφωνία: {ok == Ms.is_diagonalizable()}")
    return ok


B = np.array([[3, 1], [0, 3]], dtype=float)     # μπλοκ Jordan
diagonalizability_report(A, "A")
diagonalizability_report(B, "B")

# ── Β. (β) Φασματικό θεώρημα: S = Q·Λ·Qᵀ με eigh ──────────
print("\n── Β. (β) Ορθογώνια διαγωνοποίηση του συμμετρικού S ──")

S = np.array([[4, 2],
              [2, 1]], dtype=float)
print("S =\n", S)
print("S == Sᵀ ;  Έλεγχος:", bool(np.allclose(S, S.T)))

eigvals, Q = np.linalg.eigh(S)      # eigh → ορθοκανονικά ιδιοδιανύσματα
Lam = np.diag(eigvals)

print("Ιδιοτιμές Λ:", np.round(eigvals, 10), "  [Αναμένονται 0 και 5]")
print("Q (ορθοκανονικός) =\n", np.round(Q, 6))
print("  [στήλες: ±(1,-2)/√5 για λ=0 και ±(2,1)/√5 για λ=5]")
print("QᵀQ == I ;  Έλεγχος:", bool(np.allclose(Q.T @ Q, np.eye(2))))
print("Q⁻¹ == Qᵀ ;  Έλεγχος:", bool(np.allclose(np.linalg.inv(Q), Q.T)))
print(f"det(Q) = {np.linalg.det(Q):.6f}  (±1 για ορθογώνιο)")
print("Q·Λ·Qᵀ =\n", np.round(Q @ Lam @ Q.T, 10))
print("Q·Λ·Qᵀ == S ;  Έλεγχος:", bool(np.allclose(Q @ Lam @ Q.T, S)))

# Επαλήθευση S·q = λ·q για κάθε στήλη
for j in range(2):
    print(f"  S·q{j+1} - λ{j+1}·q{j+1} ‖·‖ ="
          f" {np.linalg.norm(S @ Q[:, j] - eigvals[j] * Q[:, j]):.2e}")

# ── Γ. (γ) SVD και προσέγγιση rank-1 ──────────────────────
print("\n── Γ. (γ) SVD: M = U·Σ·Vᵀ ──")

M = np.array([[1, 2, 0],
              [0, 1, 3],
              [1, 0, 1]], dtype=float)
print("M =\n", M)

U, sigma, Vt = np.linalg.svd(M)
Sigma = np.diag(sigma)

print("Μοναδιαίες τιμές σ:", np.round(sigma, 6))
print("U ορθογώνιος (UᵀU = I):", bool(np.allclose(U.T @ U, np.eye(3))))
print("V ορθογώνιος (VᵀV = I):", bool(np.allclose(Vt @ Vt.T, np.eye(3))))
print("U·Σ·Vᵀ == M ;  Έλεγχος:", bool(np.allclose(U @ Sigma @ Vt, M)))
print("rank(M) =", int(np.linalg.matrix_rank(M)),
      "= πλήθος μη μηδενικών σ:", int(np.sum(sigma > 1e-10)))
print(f"σ₁ = ‖M‖₂ = {sigma[0]:.6f}  Έλεγχος:",
      bool(np.isclose(sigma[0], np.linalg.norm(M, 2))))

M1 = sigma[0] * np.outer(U[:, 0], Vt[0, :])     # προσέγγιση rank-1
err = np.linalg.norm(M - M1, 'fro')
err_theory = np.sqrt(np.sum(sigma[1:] ** 2))    # θεώρημα Eckart–Young

print("\nΠροσέγγιση rank-1  M₁ = σ₁·u₁·v₁ᵀ =\n", np.round(M1, 6))
print("rank(M₁) =", int(np.linalg.matrix_rank(M1)))
print(f"Σφάλμα Frobenius ‖M - M₁‖_F = {err:.6f}")
print(f"Θεωρητική τιμή √(σ₂²+σ₃²)   = {err_theory:.6f}")
print("Ισότητα (Eckart–Young) ;  Έλεγχος:", bool(np.isclose(err, err_theory)))
print(f"Σχετικό σφάλμα = {err / np.linalg.norm(M, 'fro'):.4f}")

# ── Δ. (δ) Εκθετική πίνακα: e^(π/2·A₀) = R(π/2) ───────────
print("\n── Δ. (δ) Εκθετική πίνακα e^(π/2·A₀) ──")

A0 = np.array([[0, -1],
               [1,  0]], dtype=float)    # γεννήτορας στροφής
t = np.pi / 2

print("A₀ =\n", A0, "\n(αντισυμμετρικός: A₀ᵀ = -A₀ →",
      bool(np.allclose(A0.T, -A0)), ")")

E = sla.expm(t * A0)
R = np.array([[np.cos(t), -np.sin(t)],
              [np.sin(t),  np.cos(t)]])   # R(π/2) αναλυτικά

print(f"\ne^(π/2·A₀) (scipy.linalg.expm) =\n{np.round(E, 10)}")
print(f"R(π/2) (αναλυτικά) =\n{np.round(R, 10)}")
print("  [Αναμένεται: [[0, -1], [1, 0]] — στροφή κατά 90°]")
print("e^(π/2·A₀) == R(π/2) ;  Έλεγχος:", bool(np.allclose(E, R)))
print("Ορθογώνιος (EᵀE = I):", bool(np.allclose(E.T @ E, np.eye(2))),
      f"| det = {np.linalg.det(E):.10f} (= 1 → γνήσια στροφή)")
print("e^(π/2·A₀)·(1,0)ᵀ =", np.round(E @ np.array([1.0, 0.0]), 10),
      "  [το (1,0) πάει στο (0,1) ✓]")
print("(e^(π/2·A₀))⁴ = I ;  Έλεγχος:",
      bool(np.allclose(np.linalg.matrix_power(E, 4), np.eye(2))))

# ── Ε. (ε) Προαιρετικό: ισοσταθμικές της Q(x,y) = xᵀSx ────
print("\n── Ε. (ε) Προαιρετικό: ισοσταθμικές της τετραγωνικής μορφής ──")

xx, yy = np.meshgrid(np.linspace(-3, 3, 400), np.linspace(-3, 3, 400))
Qvals = 4 * xx ** 2 + 4 * xx * yy + yy ** 2      # = xᵀSx
pts = np.stack([xx.ravel(), yy.ravel()])
Qvals_mat = np.sum(pts * (S @ pts), axis=0).reshape(xx.shape)
print("Q(x,y) = 4x² + 4xy + y² = (2x+y)²")
print("Ταυτίζεται με τον υπολογισμό xᵀSx ;  Έλεγχος:",
      bool(np.allclose(Qvals, Qvals_mat)))
print("Επειδή λ_min = 0, οι ισοσταθμικές ΔΕΝ είναι ελλείψεις αλλά")
print("ζεύγη παράλληλων ευθειών 2x + y = ±√c (εκφυλισμένη μορφή).")
print("Q ≥ 0 παντού στο δείγμα:", bool(Qvals.min() >= -1e-12),
      f"| min = {Qvals.min():.2e}")

fig, axes = plt.subplots(1, 3, figsize=(14, 4.6))
fig.suptitle("Κεφ. 6 — Τετραγωνική μορφή, SVD, στροφή $e^{tA_0}$",
             fontsize=13, fontweight='bold')

# (1) Ισοσταθμικές της Q(x,y) = xᵀSx με τους κύριους άξονες
ax1 = axes[0]
ax1.set_title("Ισοσταθμικές $Q(x,y)=x^\\top S x$")
cs = ax1.contour(xx, yy, Qvals, levels=[1, 4, 9, 16], colors='royalblue')
ax1.clabel(cs, fontsize=8)
for j, col in zip(range(2), ['forestgreen', 'tomato']):
    ax1.annotate('', xy=Q[:, j] * 2.5, xytext=(0, 0),
                 arrowprops=dict(arrowstyle='->', color=col, lw=2.2))
    ax1.text(Q[0, j] * 2.7, Q[1, j] * 2.7,
             f'$q_{j+1}$, $\\lambda={eigvals[j]:.0f}$',
             color=col, fontsize=9, ha='center')
ax1.axhline(0, color='k', lw=0.5); ax1.axvline(0, color='k', lw=0.5)
ax1.set_xlim(-3, 3); ax1.set_ylim(-3, 3)
ax1.set_aspect('equal'); ax1.grid(True, alpha=0.3)
ax1.set_xlabel('x'); ax1.set_ylabel('y')

# (2) SVD: μοναδιαίες τιμές και σφάλμα προσέγγισης κατά τάξη
ax2 = axes[1]
ax2.set_title("SVD: $\\sigma_i$ και σφάλμα rank-$k$")
ks = [1, 2, 3]
errs = [np.linalg.norm(M - sum(sigma[i] * np.outer(U[:, i], Vt[i, :])
                               for i in range(k)), 'fro') for k in ks]
ax2.bar(np.arange(1, 4) - 0.18, sigma, width=0.36,
        color='royalblue', label='$\\sigma_i$')
ax2.bar(np.array(ks) + 0.18, errs, width=0.36,
        color='tomato', label='$\\|M-M_k\\|_F$')
for k, e in zip(ks, errs):
    ax2.text(k + 0.18, e + 0.06, f'{e:.2f}', ha='center', fontsize=8,
             color='tomato')
ax2.set_xticks([1, 2, 3]); ax2.set_xlabel("i  (ή τάξη k)")
ax2.legend(fontsize=9); ax2.grid(True, alpha=0.3, axis='y')

# (3) e^(tA₀): στροφή του (1,0) για t ∈ [0, π/2]
ax3 = axes[2]
ax3.set_title("$e^{tA_0}\\,(1,0)^\\top$ για $t\\in[0,\\pi/2]$")
ts = np.linspace(0, np.pi / 2, 60)
curve = np.array([sla.expm(tk * A0) @ np.array([1.0, 0.0]) for tk in ts])
ax3.plot(curve[:, 0], curve[:, 1], color='royalblue', lw=2.5)
ax3.annotate('', xy=curve[0], xytext=(0, 0),
             arrowprops=dict(arrowstyle='->', color='grey', lw=2))
ax3.annotate('', xy=curve[-1], xytext=(0, 0),
             arrowprops=dict(arrowstyle='->', color='tomato', lw=2))
ax3.text(1.02, 0.03, '$t=0$', fontsize=9, color='grey')
ax3.text(0.03, 1.05, '$t=\\pi/2$', fontsize=9, color='tomato')
ax3.set_xlim(-0.4, 1.4); ax3.set_ylim(-0.4, 1.4)
ax3.axhline(0, color='k', lw=0.5); ax3.axvline(0, color='k', lw=0.5)
ax3.set_aspect('equal'); ax3.grid(True, alpha=0.3)

plt.tight_layout()
print("Δημιουργήθηκαν τα γραφήματα (ισοσταθμικές, SVD, στροφή).")
plt.show()
