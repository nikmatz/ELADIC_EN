# ============================================================
# python_linsys.py
# Chapter 3 — Linear Systems
# Matzakos, N. (2026). Elements of Linear Algebra, Differential & Integral Calculus. NewTech Publications.
# ============================================================
#
# LIBRARIES:
#   numpy         → numerical solution (solve, lstsq)
#   sympy         → RREF, exact solution, classification of the system
#   matplotlib    → geometric interpretation (2D / 3D)
#
# BASIC COMMANDS:
#   np.linalg.solve(A, b)       → unique solution
#   np.linalg.lstsq(A, b)       → least squares
#   np.linalg.matrix_rank(A)    → rank
#   sympy.Matrix.rref()         → reduced row echelon form
#   sympy.linsolve()            → exact solution (infinitely many)
# ============================================================

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from sympy import Matrix, symbols, linsolve, Rational, pprint

print("=" * 55)
print(" Chapter 3: Linear Systems — Python")
print("=" * 55)

# ── A. System with a Unique Solution ─────────────────────
print("\n── A. Unique Solution ──")
#  2x +  y -  z =  8
# -3x -  y + 2z = -11
#  -2x +  y + 2z = -3

A1 = np.array([[ 2,  1, -1],
               [-3, -1,  2],
               [-2,  1,  2]], dtype=float)
b1 = np.array([8, -11, -3], dtype=float)

x1 = np.linalg.solve(A1, b1)
print(f"Solution: x={x1[0]:.4f}, y={x1[1]:.4f}, z={x1[2]:.4f}")
print(f"Check A@x = {np.round(A1 @ x1, 10)}  ✓")

# RREF with SymPy
Aug1 = Matrix([[ 2,  1, -1,  8],
               [-3, -1,  2, -11],
               [-2,  1,  2, -3]])
print("\nRREF([A|b]):")
pprint(Aug1.rref()[0])

# ── B. Classifying the System (Rouché–Capelli Theorem) ───
print("\n── B. Classification of Systems (Rouché–Capelli) ──")

def classify_system(A, b, label=""):
    """Classifies a linear system as unique/infinite/inconsistent."""
    A_sym = Matrix(A.tolist())
    Aug   = A_sym.row_join(Matrix(b.reshape(-1,1).tolist()))
    rA    = A_sym.rank()
    rAug  = Aug.rank()
    n     = A.shape[1]
    if rA != rAug:
        result = "INCONSISTENT (0 solutions)"
    elif rA == n:
        result = "UNIQUE solution"
    else:
        result = f"INFINITELY MANY solutions  (free variables: {n - rA})"
    print(f"  {label}: rank(A)={rA}, rank([A|b])={rAug}, n={n}  →  {result}")

# Unique solution
classify_system(A1, b1, "System A")

# Inconsistent
A2 = np.array([[1, 1], [2, 2]], dtype=float)
b2 = np.array([3, 5], dtype=float)
classify_system(A2, b2, "System B")

# Infinitely many solutions
A3 = np.array([[1, 2, -1], [2, 4, -2]], dtype=float)
b3 = np.array([3, 6], dtype=float)
classify_system(A3, b3, "System C")

# ── C. Infinitely Many Solutions — Parametric Form ───────
print("\n── C. Parametric Solution ──")
x, y, z = symbols('x y z')
sys3 = Matrix([[1, 2, -1, 3],
               [2, 4, -2, 6]])
rref3, pivots3 = sys3.rref()
print("RREF:"); pprint(rref3)
print(f"Pivots: {pivots3}  →  free variables: y, z")

sol3 = linsolve((Matrix([[1,2,-1],[2,4,-2]]), Matrix([3,6])), x, y, z)
print("Parametric solution:"); pprint(sol3)

# ── D. Cramer's Rule ──────────────────────────────────────
print("\n── D. Cramer's Rule ──")
A_cr = np.array([[2, 1], [5, 3]], dtype=float)
b_cr = np.array([4, 7], dtype=float)
det_A = np.linalg.det(A_cr)
print(f"det(A) = {det_A:.4f}")

for i in range(2):
    Ai = A_cr.copy()
    Ai[:, i] = b_cr
    xi = np.linalg.det(Ai) / det_A
    print(f"  {'xy'[i]} = det(A{i+1})/det(A) = {np.linalg.det(Ai):.4f}/{det_A:.4f} = {xi:.4f}")

print(f"Check: {A_cr @ np.linalg.solve(A_cr, b_cr)} ≈ {b_cr}  ✓")

# ── E. Homogeneous System ─────────────────────────────────
print("\n── E. Homogeneous System Ax = 0 ──")
A5 = Matrix([[ 1, -2,  1],
             [ 2, -3,  1],
             [ 0,  1, -1]])
print(f"rank(A) = {A5.rank()}, nullity = {3 - A5.rank()}")
print("Null space (nontrivial solutions):")
for v in A5.nullspace():
    pprint(v.T)

# ── F. Geometric Interpretation (2D) ─────────────────────
print("\n── F. Geometric Interpretation ──")

fig, axes = plt.subplots(1, 3, figsize=(14, 4))
fig.suptitle("Geometric Interpretation of Linear Systems (2D)",
             fontsize=12, fontweight='bold')
t = np.linspace(-1, 6, 300)

# Unique solution: 2x+y=7, x+3y=11
ax = axes[0]; ax.set_title("Unique Solution\n$2x+y=7$,  $x+3y=11$")
ax.plot(t, 7 - 2*t, 'royalblue', lw=2, label='$2x+y=7$')
ax.plot(t, (11 - t)/3, 'tomato', lw=2, label='$x+3y=11$')
xs = np.linalg.solve([[2,1],[1,3]], [7,11])
ax.plot(*xs, 'ko', ms=8, zorder=5)
ax.annotate(f'({xs[0]:.1f},{xs[1]:.1f})', xs, xytext=(xs[0]+0.3, xs[1]+0.3), fontsize=9)
ax.set_xlim(-1,6); ax.set_ylim(-1,6); ax.grid(True,alpha=0.3)
ax.legend(fontsize=8); ax.set_xlabel('x'); ax.set_ylabel('y')

# Inconsistent: x+y=3, x+y=5
ax = axes[1]; ax.set_title("Inconsistent\n$x+y=3$,  $x+y=5$")
ax.plot(t, 3 - t, 'royalblue', lw=2, label='$x+y=3$')
ax.plot(t, 5 - t, 'tomato', lw=2, ls='--', label='$x+y=5$')
ax.set_xlim(-1,6); ax.set_ylim(-1,6); ax.grid(True,alpha=0.3)
ax.legend(fontsize=8); ax.set_xlabel('x'); ax.set_ylabel('y')
ax.text(2, 2.5, 'Parallel\n(no common point)', fontsize=8,
        ha='center', color='gray',
        bbox=dict(boxstyle='round', fc='white', alpha=0.8))

# Infinitely many: x+y=3, 2x+2y=6
ax = axes[2]; ax.set_title("Infinitely Many Solutions\n$x+y=3$,  $2x+2y=6$")
ax.plot(t, 3 - t, 'royalblue', lw=3, label='$x+y=3$ (= $2x+2y=6$)')
ax.set_xlim(-1,6); ax.set_ylim(-1,6); ax.grid(True,alpha=0.3)
ax.legend(fontsize=8); ax.set_xlabel('x'); ax.set_ylabel('y')
ax.text(3, 1.5, 'Identical lines\n(infinitely many solutions)', fontsize=8,
        ha='center', color='gray',
        bbox=dict(boxstyle='round', fc='white', alpha=0.8))

plt.tight_layout()
plt.show()

# ============================================================
# SUPPLEMENT — Vandermonde matrix & polynomial fitting
#   np.vander, np.polyfit, np.polyval
# ============================================================
import numpy as np

# Interpolation: we find the second-degree polynomial through 3 points,
# by solving the linear system V c = y with a Vandermonde matrix.
xi = np.array([0.0, 1.0, 2.0])
yi = np.array([1.0, 3.0, 9.0])
V  = np.vander(xi, 3)          # columns: x^2, x^1, x^0
c  = np.linalg.solve(V, yi)    # coefficients (a, b, c) of ax^2+bx+c
print("Vandermonde V =\n", V)
print("Coefficients (from np.linalg.solve):", np.round(c, 6))

# The same result with np.polyfit (least squares):
c2 = np.polyfit(xi, yi, 2)
print("Coefficients (from np.polyfit)     :", np.round(c2, 6))

# Evaluating the polynomial with np.polyval:
for x0 in (0.0, 1.0, 1.5, 2.0):
    print(f"  p({x0}) = {np.polyval(c, x0):.4f}")

# Overdetermined system (more points than unknowns):
xs = np.array([0., 1., 2., 3., 4.])
ys = np.array([1.1, 2.9, 9.2, 19.1, 32.8])
cls = np.polyfit(xs, ys, 2)    # best least-squares fit
print("Least squares, degree 2:", np.round(cls, 4))
print("Residuals:", np.round(ys - np.polyval(cls, xs), 4))
