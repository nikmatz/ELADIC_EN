# ============================================================
# python_lintrans.py
# Chapter 4 — Linear Transformations
# Matzakos, N. (2026). Elements of Linear Algebra, Differential & Integral Calculus. NewTech Publications.
# ============================================================
#
# LIBRARIES:
#   numpy      → applying transformations (@ operator)
#   sympy      → kernel, image, exact solution
#   matplotlib → geometric visualization (unit circle,
#                transformation of polygons)
#
# BASIC COMMANDS:
#   A @ v                    → T(v) = applying the transformation
#   A @ B                    → composition T₂∘T₁
#   np.linalg.inv(A)         → inverse transformation
#   sympy.Matrix.nullspace() → kernel
#   sympy.Matrix.columnspace()→ image
#   np.linalg.det(A)         → det (invertibility, area)
# ============================================================

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.patches import FancyArrowPatch
from sympy import Matrix, pi, cos, sin, sqrt, Rational, pprint

print("=" * 55)
print(" Chapter 4: Linear Transformations — Python")
print("=" * 55)

# ── A. Definition & Application of a Transformation ──────
print("\n── A. Transformation T: ℝ³ → ℝ³ ──")

A = np.array([[ 1,  2,  0],
              [ 3, -1,  1],
              [ 0,  2, -1]], dtype=float)

print("A =\n", A)

# Applying it to the basis vectors
e1, e2, e3 = np.eye(3)
print(f"\nT(e₁) = {A @ e1}")
print(f"T(e₂) = {A @ e2}")
print(f"T(e₃) = {A @ e3}")

u = np.array([2, -1, 3])
print(f"\nT([2,-1,3]ᵀ) = {A @ u}")

# Test of linearity
w = np.array([1, 1, 1])
alpha, beta = 2, -1
lhs = A @ (alpha*u + beta*w)
rhs = alpha*(A @ u) + beta*(A @ w)
print(f"\nTest: T(2u-w) = {lhs}")
print(f"         2T(u)-T(w) = {rhs}")
print(f"Equality: {np.allclose(lhs, rhs)}  ✓")

# ── B. Kernel & Image ────────────────────────────────────
print("\n── B. Ker(T) & Im(T) ──")

A_sym = Matrix([[ 1,  2,  0],
                [ 3, -1,  1],
                [ 0,  2, -1]])

r = A_sym.rank()
print(f"rank(A)  = {r}  →  dim(Im) = {r}")
print(f"nullity  = {3-r}  →  dim(Ker) = {3-r}")
print(f"rank + nullity = {r} + {3-r} = 3 = n  ✓")

ker = A_sym.nullspace()
print("\nKer(T):")
if ker:
    for v in ker: pprint(v.T)
else:
    print("  {0}  (only the zero vector)")

print("\nIm(T) — basis:")
for v in A_sym.columnspace(): pprint(v.T)

# ── C. Geometric Transformations in ℝ² ──────────────────
print("\n── C. Geometric Transformations ──")

def rot(theta_deg):
    """Rotation matrix through t degrees."""
    t = np.radians(theta_deg)
    return np.array([[np.cos(t), -np.sin(t)],
                     [np.sin(t),  np.cos(t)]])

def ref_x():
    return np.array([[1, 0], [0, -1]])

def scale(sx, sy):
    return np.array([[sx, 0], [0, sy]])

def shear(k):
    """Shear along x."""
    return np.array([[1, k], [0, 1]])

R45  = rot(45)
R90  = rot(90)
Refx = ref_x()
Sc   = scale(2, 0.5)
Sh   = shear(1)

print(f"R₄₅·(1,0)ᵀ = {np.round(R45 @ [1,0], 6)}")
print(f"  (= (√2/2, √2/2) ≈ (0.7071, 0.7071) ✓)")
print(f"det(R₄₅) = {np.linalg.det(R45):.6f}  (= 1 → area preserving ✓)")
print(f"det(Ref_x) = {np.linalg.det(Refx):.1f}  (= -1 → reverses orientation)")
print(f"det(Scale(2,0.5)) = {np.linalg.det(Sc):.4f}  (= 2·0.5 = 1)")

# Composition: non-commutative
print(f"\nR₉₀∘Ref_x =\n{np.round(R90 @ Refx, 6)}")
print(f"Ref_x∘R₉₀ =\n{np.round(Refx @ R90, 6)}")
print("Different!  →  non-commutativity ✓")

# ── D. Graphical Representation ────────────────────────────
print("\n── D. Graphical Representation ──")

# Unit square (+ closed)
sq = np.array([[0,1,1,0,0],
               [0,0,1,1,0]], dtype=float)

fig, axes = plt.subplots(2, 3, figsize=(13, 8))
fig.suptitle("Geometric Linear Transformations", fontsize=13, fontweight='bold')

transforms = [
    (np.eye(2),  "Identity $I$"),
    (R45,        "Rotation $45°$"),
    (R90,        "Rotation $90°$"),
    (Refx,       "Reflection in $x$"),
    (Sc,         "Scaling\n$s_x=2, s_y=0.5$"),
    (Sh,         "Shear $k=1$"),
]

for ax, (T, title) in zip(axes.flat, transforms):
    sq_t = T @ sq
    ax.fill(sq[0], sq[1], alpha=0.25, color='royalblue', label='Original')
    ax.fill(sq_t[0], sq_t[1], alpha=0.35, color='tomato', label='After T')
    ax.plot(sq[0], sq[1], 'royalblue', lw=1.5)
    ax.plot(sq_t[0], sq_t[1], 'tomato', lw=2)
    ax.axhline(0, color='k', lw=0.5); ax.axvline(0, color='k', lw=0.5)
    ax.set_xlim(-2.2, 2.2); ax.set_ylim(-2.2, 2.2)
    ax.set_aspect('equal'); ax.grid(True, alpha=0.3)
    ax.set_title(title, fontsize=9)
    det_T = np.linalg.det(T)
    ax.set_xlabel(f"det = {det_T:.3f}", fontsize=8)
    ax.legend(fontsize=7, loc='upper right')

plt.tight_layout()
plt.show()
