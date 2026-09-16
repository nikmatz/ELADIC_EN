# ============================================================
# python_diag.py
# Chapter 6 — Diagonalization, SVD, e^A, Quadratic Forms
# Matzakos, N. (2026). Elements of Linear Algebra, Differential & Integral Calculus. NewTech Publications.
# ============================================================
#
# LIBRARIES:
#   numpy         → eig, eigh, svd, matrix_power
#   scipy.linalg  → expm (matrix exponential)
#   sympy         → exact test of diagonalizability
#   matplotlib    → level curves of a quadratic form, SVD, rotation
#
# BASIC COMMANDS:
#   np.linalg.eig(A)         → diagonalization (general): A = P·D·P⁻¹
#   np.linalg.eigh(S)        → symmetric matrices: ORTHONORMAL eigenvectors
#   np.linalg.svd(M)         → SVD: M = U·Sigma·Vᵀ
#   scipy.linalg.expm(A)     → matrix exponential e^A
#   np.linalg.matrix_power   → Aⁿ directly (for comparison)
#   plt.contour(...)         → level curves
#
# Book activity: (a) diagonalization of A and A¹⁰,
#   (b) the spectral theorem for S, (c) SVD & rank-1 approximation,
#   (d) e^(pi/2·A₀) = R(pi/2), (e) level curves of xᵀSx.
# ============================================================

import numpy as np
import scipy.linalg as sla
import matplotlib.pyplot as plt
from sympy import Matrix, nsimplify

print("=" * 58)
print(" Chapter 6: Diagonalization, SVD, e^A — Python")
print("=" * 58)

# ── A. (a) Diagonalization A = P·D·P⁻¹ and A¹⁰ ─────────────
print("\n── A. (a) Diagonalization A = P·D·P⁻¹ ──")

A = np.array([[5, 4],
              [1, 2]], dtype=float)
print("A =\n", A)

vals, P = np.linalg.eig(A)
D = np.diag(vals)
P_inv = np.linalg.inv(P)

print("Eigenvalues:", np.round(vals, 10), "  [Expected 6 and 1]")
print("P (columns = eigenvectors) =\n", np.round(P, 6))
print(f"det(P) = {np.linalg.det(P):.6f} ≠ 0 → P is invertible:",
      bool(not np.isclose(np.linalg.det(P), 0)))
print("P·D·P⁻¹ =\n", np.round(P @ D @ P_inv, 10))
print("P·D·P⁻¹ == A ;  Check:", bool(np.allclose(P @ D @ P_inv, A)))

n_pow = 10
A_pow_diag = P @ np.diag(vals ** n_pow) @ P_inv
A_pow_direct = np.linalg.matrix_power(A, n_pow)
print("\nA¹⁰ = P·D¹⁰·P⁻¹ =\n", np.round(A_pow_diag, 4))
print("A¹⁰ = np.linalg.matrix_power(A,10) =\n", A_pow_direct)
print("  [Expected: [[48372941, 48372940], [12093235, 12093236]]]")
print("The two computations agree ;  Check:",
      bool(np.allclose(A_pow_diag, A_pow_direct)))
print("They match the expected value:",
      bool(np.allclose(A_pow_direct,
                       [[48372941, 48372940], [12093235, 12093236]])))

# Supplement (corresponds to part (b) of the Maxima activity):
# why B = [[3,1],[0,3]] is NOT diagonalizable.
print("\nSupplement: test of diagonalizability")


def diagonalizability_report(M, name):
    """Compares the algebraic and geometric multiplicity of each eigenvalue.
    Diagonalizable ⇔ sum(m_g) = n (NOT from the rank of a single M - lam·I).
    NOTE: the test is carried out EXACTLY (nsimplify), because with decimals
    SymPy "splits" a double eigenvalue into two simple ones due to rounding."""
    Ms = Matrix(M.tolist()).applyfunc(nsimplify)
    n = M.shape[0]
    total_geo = 0
    for eigval, m_a, vecs in Ms.eigenvects():
        m_g = len(vecs)
        total_geo += m_g
        print(f"  {name}: lam = {eigval}  m_a = {m_a}  m_g = {m_g}"
              f"  {'(defective)' if m_g < m_a else ''}")
    ok = (total_geo == n)
    print(f"  sum(m_g) = {total_geo} (n = {n}) → diagonalizable: {ok}")
    # Cross-check with SymPy's own tester
    print(f"  SymPy is_diagonalizable(): {Ms.is_diagonalizable()}"
          f"  | agreement: {ok == Ms.is_diagonalizable()}")
    return ok


B = np.array([[3, 1], [0, 3]], dtype=float)     # Jordan block
diagonalizability_report(A, "A")
diagonalizability_report(B, "B")

# ── B. (b) Spectral theorem: S = Q·Lambda·Qᵀ with eigh ────
print("\n── B. (b) Orthogonal diagonalization of the symmetric S ──")

S = np.array([[4, 2],
              [2, 1]], dtype=float)
print("S =\n", S)
print("S == Sᵀ ;  Check:", bool(np.allclose(S, S.T)))

eigvals, Q = np.linalg.eigh(S)      # eigh → orthonormal eigenvectors
Lam = np.diag(eigvals)

print("Eigenvalues Lambda:", np.round(eigvals, 10), "  [Expected 0 and 5]")
print("Q (orthonormal) =\n", np.round(Q, 6))
print("  [columns: ±(1,-2)/√5 for lam=0 and ±(2,1)/√5 for lam=5]")
print("QᵀQ == I ;  Check:", bool(np.allclose(Q.T @ Q, np.eye(2))))
print("Q⁻¹ == Qᵀ ;  Check:", bool(np.allclose(np.linalg.inv(Q), Q.T)))
print(f"det(Q) = {np.linalg.det(Q):.6f}  (±1 for an orthogonal matrix)")
print("Q·Lambda·Qᵀ =\n", np.round(Q @ Lam @ Q.T, 10))
print("Q·Lambda·Qᵀ == S ;  Check:", bool(np.allclose(Q @ Lam @ Q.T, S)))

# Check S·q = lam·q for every column
for j in range(2):
    print(f"  S·q{j+1} - lam{j+1}·q{j+1} ‖·‖ ="
          f" {np.linalg.norm(S @ Q[:, j] - eigvals[j] * Q[:, j]):.2e}")

# ── C. (c) SVD and rank-1 approximation ──────────────────
print("\n── C. (c) SVD: M = U·Sigma·Vᵀ ──")

M = np.array([[1, 2, 0],
              [0, 1, 3],
              [1, 0, 1]], dtype=float)
print("M =\n", M)

U, sigma, Vt = np.linalg.svd(M)
Sigma = np.diag(sigma)

print("Singular values sigma:", np.round(sigma, 6))
print("U orthogonal (UᵀU = I):", bool(np.allclose(U.T @ U, np.eye(3))))
print("V orthogonal (VᵀV = I):", bool(np.allclose(Vt @ Vt.T, np.eye(3))))
print("U·Sigma·Vᵀ == M ;  Check:", bool(np.allclose(U @ Sigma @ Vt, M)))
print("rank(M) =", int(np.linalg.matrix_rank(M)),
      "= number of nonzero sigma:", int(np.sum(sigma > 1e-10)))
print(f"sigma_1 = ‖M‖₂ = {sigma[0]:.6f}  Check:",
      bool(np.isclose(sigma[0], np.linalg.norm(M, 2))))

M1 = sigma[0] * np.outer(U[:, 0], Vt[0, :])     # rank-1 approximation
err = np.linalg.norm(M - M1, 'fro')
err_theory = np.sqrt(np.sum(sigma[1:] ** 2))    # Eckart–Young theorem

print("\nRank-1 approximation  M₁ = sigma_1·u₁·v₁ᵀ =\n", np.round(M1, 6))
print("rank(M₁) =", int(np.linalg.matrix_rank(M1)))
print(f"Frobenius error ‖M - M₁‖_F = {err:.6f}")
print(f"Theoretical value √(sigma_2²+sigma_3²) = {err_theory:.6f}")
print("Equality (Eckart–Young) ;  Check:", bool(np.isclose(err, err_theory)))
print(f"Relative error = {err / np.linalg.norm(M, 'fro'):.4f}")

# ── D. (d) Matrix exponential: e^(pi/2·A₀) = R(pi/2) ──────
print("\n── D. (d) Matrix exponential e^(pi/2·A₀) ──")

A0 = np.array([[0, -1],
               [1,  0]], dtype=float)    # generator of rotation
t = np.pi / 2

print("A₀ =\n", A0, "\n(skew-symmetric: A₀ᵀ = -A₀ →",
      bool(np.allclose(A0.T, -A0)), ")")

E = sla.expm(t * A0)
R = np.array([[np.cos(t), -np.sin(t)],
              [np.sin(t),  np.cos(t)]])   # R(pi/2) analytically

print(f"\ne^(pi/2·A₀) (scipy.linalg.expm) =\n{np.round(E, 10)}")
print(f"R(pi/2) (analytically) =\n{np.round(R, 10)}")
print("  [Expected: [[0, -1], [1, 0]] — rotation by 90°]")
print("e^(pi/2·A₀) == R(pi/2) ;  Check:", bool(np.allclose(E, R)))
print("Orthogonal (EᵀE = I):", bool(np.allclose(E.T @ E, np.eye(2))),
      f"| det = {np.linalg.det(E):.10f} (= 1 → proper rotation)")
print("e^(pi/2·A₀)·(1,0)ᵀ =", np.round(E @ np.array([1.0, 0.0]), 10),
      "  [(1,0) is mapped to (0,1) ✓]")
print("(e^(pi/2·A₀))⁴ = I ;  Check:",
      bool(np.allclose(np.linalg.matrix_power(E, 4), np.eye(2))))

# ── E. (e) Optional: level curves of Q(x,y) = xᵀSx ───────
print("\n── E. (e) Optional: level curves of the quadratic form ──")

xx, yy = np.meshgrid(np.linspace(-3, 3, 400), np.linspace(-3, 3, 400))
Qvals = 4 * xx ** 2 + 4 * xx * yy + yy ** 2      # = xᵀSx
pts = np.stack([xx.ravel(), yy.ravel()])
Qvals_mat = np.sum(pts * (S @ pts), axis=0).reshape(xx.shape)
print("Q(x,y) = 4x² + 4xy + y² = (2x+y)²")
print("Identical with the computation xᵀSx ;  Check:",
      bool(np.allclose(Qvals, Qvals_mat)))
print("Since lam_min = 0, the level curves are NOT ellipses but")
print("pairs of parallel lines 2x + y = ±√c (degenerate form).")
print("Q ≥ 0 everywhere in the sample:", bool(Qvals.min() >= -1e-12),
      f"| min = {Qvals.min():.2e}")

fig, axes = plt.subplots(1, 3, figsize=(14, 4.6))
fig.suptitle("Ch. 6 — Quadratic form, SVD, rotation $e^{tA_0}$",
             fontsize=13, fontweight='bold')

# (1) Level curves of Q(x,y) = xᵀSx with the principal axes
ax1 = axes[0]
ax1.set_title("Level curves $Q(x,y)=x^\\top S x$")
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

# (2) SVD: singular values and approximation error by rank
ax2 = axes[1]
ax2.set_title("SVD: $\\sigma_i$ and rank-$k$ error")
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
ax2.set_xticks([1, 2, 3]); ax2.set_xlabel("i  (or rank k)")
ax2.legend(fontsize=9); ax2.grid(True, alpha=0.3, axis='y')

# (3) e^(tA₀): rotation of (1,0) for t ∈ [0, pi/2]
ax3 = axes[2]
ax3.set_title("$e^{tA_0}\\,(1,0)^\\top$ for $t\\in[0,\\pi/2]$")
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
print("The plots have been created (level curves, SVD, rotation).")
plt.show()
