# ============================================================
# python_matrices.py
# Chapter 2 — Matrices, NumPy, LU Decomposition, Heatmaps
# Matzakos, N. (2026). Elements of Linear Algebra, Differential & Integral Calculus. NewTech Publications.
# ============================================================
#
# LIBRARIES:
#   numpy         → numerical matrix operations
#   scipy.linalg  → LU decomposition
#   sympy         → exact computations (fractions)
#   matplotlib    → visualization (matrix heatmaps)
#
# BASIC COMMANDS:
#   A @ B                  → matrix product
#   A.T                    → transpose
#   np.linalg.det(A)       → determinant
#   np.linalg.inv(A)       → inverse
#   np.linalg.solve(A, b)  → solution of A·x = b
#   scipy.linalg.lu(A)     → decomposition A = P·L·U
#   np.linalg.eigh(S)      → eigenvalues of a symmetric matrix
#
# Book activity: (a) NumPy operations, (b) solving A·x = b,
#   (c) A = P·L·U, (d) positive definiteness of S, (e) heatmaps.
# ============================================================

import numpy as np
import scipy.linalg as la
import matplotlib.pyplot as plt
import matplotlib.colors as mcolors
from sympy import Matrix, pprint

print("=" * 58)
print(" Chapter 2: Matrices, LU, Heatmaps — Python")
print("=" * 58)

# Data of the Maxima activity (same A, B, b)
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

# ── A. (a) Operations with NumPy — comparison with Maxima ─
print("\n── A. (a) Operations with NumPy ──")

AB = A @ B
BA = B @ A

print("A @ B =\n", AB)
print("  [Maxima: matrix([4,11,14],[1,11,17],[16,13,6])] →",
      np.allclose(AB, [[4, 11, 14], [1, 11, 17], [16, 13, 6]]))
print("\nB @ A =\n", BA)
print("A@B == B@A ;  Check:", np.allclose(AB, BA))
print("  → False: matrix multiplication is not commutative")

print("\nAᵀ =\n", A.T)
print("(A@B)ᵀ == Bᵀ@Aᵀ ;  Check:", np.allclose(AB.T, B.T @ A.T))

det_A = np.linalg.det(A)
det_B = np.linalg.det(B)
det_AB = np.linalg.det(AB)
print(f"\ndet(A)  = {det_A:.10f}   [Maxima: 1]")
print(f"det(B)  = {det_B:.10f}   [Maxima: 24]")
print(f"det(AB) = {det_AB:.10f}   [Maxima: 24]")
print("det(A·B) == det(A)·det(B) ;  Check:",
      np.isclose(det_AB, det_A * det_B))

A_inv = np.linalg.inv(A)
print("\nA⁻¹ =\n", np.round(A_inv, 10))
print("  [Maxima: matrix([-24,18,5],[20,-15,-4],[-5,4,1])] →",
      np.allclose(A_inv, [[-24, 18, 5], [20, -15, -4], [-5, 4, 1]]))
print("A @ A⁻¹ =\n", np.round(A @ A_inv, 10))
print("A·A⁻¹ == I₃ ;  Check:", np.allclose(A @ A_inv, np.eye(3)))

# Exact (rational) computation with SymPy — comparison with Maxima
A_sym = Matrix([[1, 2, 3], [0, 1, 4], [5, 6, 0]])
print("\nExact A⁻¹ (SymPy):")
pprint(A_sym.inv())

# ── B. (b) Solving A·x = b ────────────────────────────────
print("\n── B. (b) Solving A·x = b ──")

x = np.linalg.solve(A, b)
print("x = np.linalg.solve(A, b) =", np.round(x, 10))
print("  [Expected: (27, -22, 6)] →", np.allclose(x, [27, -22, 6]))
print("A @ x =", np.round(A @ x, 10))
print("A·x == b ;  Check:", np.allclose(A @ x, b))
print(f"Residual ‖A·x - b‖ = {np.linalg.norm(A @ x - b):.2e}")

# Exact solution with SymPy
print("\nx (SymPy, exact):",
      list(A_sym.solve(Matrix([1, 2, 3]))))

# ── C. (c) Decomposition A = P·L·U ────────────────────────
print("\n── C. (c) LU Decomposition ──")

P, L, U = la.lu(A)

print("P (permutation matrix) =\n", P)
print("\nL (lower triangular, ones on the diagonal) =\n", np.round(L, 6))
print("\nU (upper triangular) =\n", np.round(U, 6))
print("\nP @ L @ U =\n", np.round(P @ L @ U, 10))
print("P·L·U == A ;  Check:", np.allclose(P @ L @ U, A))
print("L lower triangular:", np.allclose(L, np.tril(L)),
      "| U upper triangular:", np.allclose(U, np.triu(U)))
print(f"det(A) = ±det(U) = {np.linalg.det(P) * np.prod(np.diag(U)):.10f}",
      "  Check:",
      np.isclose(np.linalg.det(P) * np.prod(np.diag(U)), det_A))

# ── D. (d) Symmetric S: eigenvalues & positive definiteness ─
print("\n── D. (d) Symmetric S — np.linalg.eigh ──")

S = np.array([[4, 2, 1],
              [2, 5, 3],
              [1, 3, 6]], dtype=float)

print("S =\n", S)
print("S == Sᵀ ;  Check:", np.allclose(S, S.T))

eigvals, eigvecs = np.linalg.eigh(S)     # eigh: symmetric → real eigenvalues
print("\nEigenvalues (eigh):", np.round(eigvals, 6))
print("Eigenvectors (columns of Q):\n", np.round(eigvecs, 6))
print("QᵀQ == I ;  Check:", np.allclose(eigvecs.T @ eigvecs, np.eye(3)))
print("Q·D·Qᵀ == S ;  Check:",
      np.allclose(eigvecs @ np.diag(eigvals) @ eigvecs.T, S))

# Criterion 1: all eigenvalues > 0
pd_eig = bool(np.all(eigvals > 0))
# Criterion 2 (Sylvester): all leading principal minors > 0
minors = [float(np.linalg.det(S[:k, :k])) for k in (1, 2, 3)]
pd_minors = all(m > 0 for m in minors)
# Criterion 3: a Cholesky factorization exists
try:
    np.linalg.cholesky(S)
    pd_chol = True
except np.linalg.LinAlgError:
    pd_chol = False

print(f"\nLeading principal minors: {[round(m, 6) for m in minors]}"
      "   [Expected 4, 16, 67]")
print(f"Eigenvalue criterion (all eigenvalues > 0): {pd_eig}")
print(f"Sylvester criterion  (minors > 0):          {pd_minors}")
print(f"Cholesky criterion   (L exists):            {pd_chol}")
print("→ S is positive definite:",
      pd_eig and pd_minors and pd_chol)
print("NOTE: det(S) > 0 ALONE is not enough "
      "(e.g. -I₂ has det = 1 > 0 but is negative definite).")

# Test with random vectors: xᵀSx > 0 for every x ≠ 0
rng = np.random.default_rng(0)
X = rng.normal(size=(3, 200))
qvals = np.sum(X * (S @ X), axis=0)
print(f"min(xᵀSx) over 200 random x: {qvals.min():.6f} > 0 →",
      bool(qvals.min() > 0))

# ── E. (e) Optional: Heatmaps of A, A·B and L ─────────────
print("\n── E. (e) Heatmaps (optional) ──")

fig, axes = plt.subplots(1, 3, figsize=(13, 4))
fig.suptitle("Ch. 2 — Matrix heatmaps", fontsize=13, fontweight='bold')


def plot_matrix(ax, M, title, fmt=".1f"):
    """Display a matrix as a heatmap with the numerical values."""
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


plot_matrix(axes[0], A,  "Matrix A")
plot_matrix(axes[1], AB, "A · B")
plot_matrix(axes[2], L,  "L (from A = P·L·U)")

plt.tight_layout()
print("Created a heatmap for A, A·B and L.")
plt.show()
