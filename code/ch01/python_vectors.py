# ============================================================
# python_vectors.py
# Chapter 1 — Linear Vector Spaces
# Matzakos, N. (2026). Elements of Linear Algebra, Differential & Integral Calculus. NewTech Publications.
# ============================================================
#
# LIBRARIES:
#   numpy    → linear algebra (rank, det, SVD, null space)
#   scipy    → additional tools (null_space)
#   sympy    → exact computations (rref, symbolic GS)
#   matplotlib → visualization of vectors in R²/R³
#
# BASIC COMMANDS:
#   np.linalg.det(A)        → determinant
#   np.linalg.matrix_rank(A)→ rank
#   np.linalg.svd(A)        → SVD decomposition
#   sympy.Matrix(A).rref()  → reduced row echelon form (RREF)
#   sympy.Matrix(A).nullspace()  → null space
#   sympy.Matrix(A).columnspace()→ column space
# ============================================================

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from sympy import Matrix, Rational, sqrt, symbols, pprint

print("=" * 55)
print(" Chapter 1: Linear Vector Spaces — Python")
print("=" * 55)

# ── A. Matrix, Determinant, Rank ─────────────────────────
print("\n── A. Analysis of a Matrix ──")

A = np.array([[1, 2, 1],
              [2, 1, 3],
              [1, 3, -1]], dtype=float)

print("Matrix A:")
print(A)
print(f"\ndet(A) = {np.linalg.det(A):.4f}")
print(f"rank(A) = {np.linalg.matrix_rank(A)}")

# ── B. RREF and Spaces (SymPy — exact) ───────────────────
print("\n── B. RREF & Spaces (SymPy) ──")

A_sym = Matrix([[1, 2, 1],
                [2, 1, 3],
                [1, 3, -1]])

rref_A, pivots = A_sym.rref()
print("RREF(A):")
pprint(rref_A)
print(f"Pivot columns: {pivots}")

print("\nNull space — Ax=0:")
ns = A_sym.nullspace()
if ns:
    for i, v in enumerate(ns):
        print(f"  v{i+1} =", end=" ")
        pprint(v.T)
else:
    print("  Trivial (zero) — A is invertible")

print("\nColumn space:")
cs = A_sym.columnspace()
for i, v in enumerate(cs):
    print(f"  c{i+1} =", end=" ")
    pprint(v.T)

# ── C. Linear Independence ────────────────────────────────
print("\n── C. Linear Independence ──")

v1 = np.array([1, 0, 1])
v2 = np.array([0, 1, 1])
v3 = np.array([1, 1, 2])   # v3 = v1 + v2  → dependent

M = np.column_stack([v1, v2, v3])
r = np.linalg.matrix_rank(M)

print(f"v₁ = {v1}")
print(f"v₂ = {v2}")
print(f"v₃ = {v3}  ← v₃ = v₁ + v₂")
print(f"\nrank([v₁|v₂|v₃]) = {r}")
print(f"→ rank = {r} < 3  ⇒  linearly DEPENDENT ✓")

# Independent sets
w1 = np.array([1, 1, 0])
w2 = np.array([1, 0, 1])
w3 = np.array([0, 1, 1])
N = np.column_stack([w1, w2, w3])
print(f"\nw₁={w1}, w₂={w2}, w₃={w3}")
print(f"rank([w₁|w₂|w₃]) = {np.linalg.matrix_rank(N)}")
print(f"→ rank = 3  ⇒  linearly INDEPENDENT ✓")

# ── D. Gram-Schmidt Orthonormalization ────────────────────
print("\n── D. Gram-Schmidt ──")

def gram_schmidt(vectors):
    """Gram-Schmidt orthonormalization of a set of vectors."""
    orthonormal = []
    for v in vectors:
        w = v.copy().astype(float)
        for e in orthonormal:
            w -= np.dot(w, e) * e   # subtract the projection
        norm = np.linalg.norm(w)
        if norm > 1e-10:            # if it is not zero
            orthonormal.append(w / norm)
    return orthonormal

basis = [w1.astype(float), w2.astype(float), w3.astype(float)]
ONB   = gram_schmidt(basis)

print("Initial basis: w₁, w₂, w₃")
print("Orthonormal basis {e₁, e₂, e₃}:")
for i, e in enumerate(ONB):
    print(f"  e{i+1} = {np.round(e, 6)}")

# Verification of orthogonality
print("\nVerification of the inner products:")
print(f"  e₁·e₂ = {ONB[0] @ ONB[1]:.10f}  (≈ 0 ✓)")
print(f"  e₁·e₃ = {ONB[0] @ ONB[2]:.10f}  (≈ 0 ✓)")
print(f"  e₂·e₃ = {ONB[1] @ ONB[2]:.10f}  (≈ 0 ✓)")
print(f"  |e₁|  = {np.linalg.norm(ONB[0]):.6f}  (= 1 ✓)")

# Building the matrix Q and verifying Q·Qᵀ = I
Q = np.column_stack(ONB)
QQT = Q @ Q.T
print("\nQ·Qᵀ ≈ I₃:")
print(np.round(QQT, 8))
print("✓ Orthonormal matrix verified")

# ── E. Graphical Representation ────────────────────────────
print("\n── E. Graphical Representation ──")

fig = plt.figure(figsize=(13, 5))
fig.suptitle("Linear Vector Spaces — Vectors in ℝ³",
             fontsize=13, fontweight='bold')

# --- Left: Linear dependence ---
ax1 = fig.add_subplot(121, projection='3d')
ax1.set_title("Linear Dependence\n$v_3 = v_1 + v_2$")
origin = [0, 0, 0]
vecs  = [v1, v2, v3]
colors = ['royalblue', 'tomato', 'forestgreen']
labels = ['$v_1=(1,0,1)$', '$v_2=(0,1,1)$', '$v_3=v_1+v_2$']
for v, col, lbl in zip(vecs, colors, labels):
    ax1.quiver(*origin, *v, color=col, arrow_length_ratio=0.15,
               linewidth=2, label=lbl)
ax1.set_xlim([0, 1.5]); ax1.set_ylim([0, 1.5]); ax1.set_zlim([0, 2.5])
ax1.set_xlabel('x'); ax1.set_ylabel('y'); ax1.set_zlabel('z')
ax1.legend(fontsize=8, loc='upper left')

# --- Right: Gram-Schmidt orthonormal basis ---
ax2 = fig.add_subplot(122, projection='3d')
ax2.set_title("Orthonormal Basis (Gram-Schmidt)")
colors2 = ['royalblue', 'tomato', 'forestgreen']
labels2 = ['$e_1$', '$e_2$', '$e_3$']
for e, col, lbl in zip(ONB, colors2, labels2):
    ax2.quiver(*origin, *e, color=col, arrow_length_ratio=0.15,
               linewidth=2.5, label=lbl)
ax2.set_xlim([-0.8, 1]); ax2.set_ylim([-0.8, 1]); ax2.set_zlim([-0.8, 1])
ax2.set_xlabel('x'); ax2.set_ylabel('y'); ax2.set_zlabel('z')
ax2.legend(fontsize=8, loc='upper left')

plt.tight_layout()
plt.show()
