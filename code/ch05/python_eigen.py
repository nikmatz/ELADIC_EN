# ============================================================
# python_eigen.py
# Chapter 5 — Eigenvalues, NumPy, Eigenspaces, Markov
# Matzakos, N. (2026). Elements of Linear Algebra, Differential & Integral Calculus. NewTech Publications.
# ============================================================
#
# LIBRARIES:
#   numpy         → numerical eigenvalues (eig), powers of matrices
#   sympy         → exact eigenvalues, eigenspaces, characteristic polynomial
#   matplotlib    → convergence of power iteration & of a Markov chain
#
# BASIC COMMANDS:
#   sympy.Matrix.eigenvects()  → (lam, m_a, [eigenvectors]) exactly
#   sympy.Matrix.charpoly()    → characteristic polynomial
#   np.linalg.eig(A)           → eigenvalues + eigenvectors (numerically)
#   np.linalg.matrix_power(M,n)→ Mⁿ
#   np.diag(v)                 → diagonal matrix
#
# Book activity: (a) exact eigenvalues/eigenvectors of A,
#   (b) numerical check of A·v = lam·v, (c) the defective matrix
#   [[3,1],[0,3]], (d) Markov stationary distribution, (e) plots.
# ============================================================

import numpy as np
import matplotlib.pyplot as plt
from sympy import Matrix, Symbol, Rational, factor

print("=" * 58)
print(" Chapter 5: Eigenvalues & Eigenspaces — Python")
print("=" * 58)

# ── A. (a) Exact eigenvalues/eigenvectors with SymPy ──────
print("\n── A. (a) SymPy: eigenvects, trace, det ──")

A_sym = Matrix([[4, 1],
                [2, 3]])
lam = Symbol('lambda')

print("A =", A_sym.tolist())
print("p(lam) = det(A - lam·I) =", factor(A_sym.charpoly(lam).as_expr()))
print("  [Expected: (lam-5)(lam-2) ✓]")

print("\neigenvects(A):")
eig_list = []          # list of the eigenvalues WITH their multiplicities
for eigval, m_a, vecs in A_sym.eigenvects():
    eig_list.extend([eigval] * m_a)
    print(f"  lam = {eigval}   (algebraic multiplicity m_a = {m_a},"
          f" geometric m_g = {len(vecs)})")
    for v in vecs:
        print("    eigenvector vᵀ =", list(v))
        print("    A·v = lam·v ;  Check:", (A_sym * v) == (eigval * v))

tr_A, det_A = A_sym.trace(), A_sym.det()
sum_l = sum(eig_list)             # sum WITH the multiplicities
prod_l = 1
for e in eig_list:
    prod_l *= e

print(f"\ntr(A) = {tr_A} | sum(lam_i) = {sum_l} | Equality: {tr_A == sum_l}")
print(f"det(A) = {det_A} | prod(lam_i) = {prod_l} | Equality: {det_A == prod_l}")
print("  [Expected tr = 7 = 5+2, det = 10 = 5·2 ✓]")

# ── B. (b) Numerical check of A·v = lam·v (NumPy) ─────────
print("\n── B. (b) NumPy: np.linalg.eig and A·v = lam·v ──")

A = np.array([[4, 1],
              [2, 3]], dtype=float)

vals, vecs = np.linalg.eig(A)
print("Eigenvalues:", np.round(vals, 10))

all_ok = True
for i in range(len(vals)):
    lv, v = vals[i], vecs[:, i]
    res = A @ v - lv * v
    ok = bool(np.allclose(res, 0))
    all_ok = all_ok and ok
    print(f"  lam{i+1} = {lv:.6f}  v{i+1} = {np.round(v, 6)}")
    print(f"    A·v = {np.round(A @ v, 6)}   lam·v = {np.round(lv * v, 6)}")
    print(f"    ‖A·v - lam·v‖ = {np.linalg.norm(res):.2e}  →  {ok}")
print("All the relations A·v = lam·v are verified:", all_ok)

# Diagonalization: A = P·D·P⁻¹ (useful in (e))
P = vecs
D = np.diag(vals)
print("P·D·P⁻¹ == A ;  Check:",
      bool(np.allclose(P @ D @ np.linalg.inv(P), A)))

# ── C. (c) The defective matrix [[3,1],[0,3]] ─────────────
print("\n── C. (c) Defective eigenvalue: B = [[3,1],[0,3]] ──")

B_sym = Matrix([[3, 1],
                [0, 3]])
print("B =", B_sym.tolist())
print("p(lam) =", factor(B_sym.charpoly(lam).as_expr()),
      "  [Expected: (lam-3)² ✓]")
print("eigenvals(B) =", B_sym.eigenvals(), "  → lam = 3 with m_a = 2")

for eigval, m_a, vecs_b in B_sym.eigenvects():
    m_g = len(vecs_b)
    print(f"\n  lam = {eigval}")
    print(f"  algebraic multiplicity  m_a = {m_a}")
    print(f"  eigenspace ker(B - lam·I) = span{[list(v) for v in vecs_b]}")
    print(f"  geometric multiplicity m_g = dim ker = {m_g}")
    print(f"  m_g < m_a ;  Check: {m_g < m_a}"
          f"  ({m_g} < {m_a})")
    if m_g < m_a:
        print("  → The eigenvalue is DEFECTIVE")

# The eigenspace also through the null space of B - 3I
N = (B_sym - 3 * Matrix.eye(2)).nullspace()
print("\nnullspace(B - 3I) =", [list(v) for v in N],
      " | dimension =", len(N))
print("rank(B - 3I) =", (B_sym - 3 * Matrix.eye(2)).rank(),
      " → dim ker = 2 - rank =", 2 - (B_sym - 3 * Matrix.eye(2)).rank())
print("B is diagonalizable:", B_sym.is_diagonalizable(),
      " (2 linearly independent eigenvectors were needed, there is 1)")

# ── D. (d) Markov chain: stationary distribution ──────────
print("\n── D. (d) Markov chain — stationary distribution pi ──")

M = np.array([[0.8, 0.3],
              [0.2, 0.7]])
print("M =\n", M)
print("Column stochastic (columns sum to 1):",
      bool(np.allclose(M.sum(axis=0), 1.0)))

M_vals, M_vecs = np.linalg.eig(M)
print("Eigenvalues of M:", np.round(M_vals, 10),
      " → there is lam = 1:", bool(np.any(np.isclose(M_vals, 1.0))))

idx = int(np.argmin(np.abs(M_vals - 1.0)))
pi = M_vecs[:, idx].real
pi = pi / pi.sum()                     # normalization to a distribution
print("pi =", np.round(pi, 10), "  [Expected (0.6, 0.4)]")
print("Sum of pi = ", round(float(pi.sum()), 10))
print("M·pi =", np.round(M @ pi, 10))
print("M·pi == pi ;  Check:", bool(np.allclose(M @ pi, pi)))

# Exact computation with SymPy (rational numbers)
M_sym = Matrix([[Rational(8, 10), Rational(3, 10)],
                [Rational(2, 10), Rational(7, 10)]])
ns = (M_sym - Matrix.eye(2)).nullspace()[0]
pi_exact = ns / sum(ns)
print("pi (exact, SymPy) =", list(pi_exact), "  [= (3/5, 2/5) ✓]")
print("M·pi = pi (exactly) ;  Check:", (M_sym * pi_exact) == pi_exact)

# Convergence Mⁿ → [pi | pi]
M50 = np.linalg.matrix_power(M, 50)
print("\nM⁵⁰ =\n", np.round(M50, 10))
print("Every column of M⁵⁰ equals pi ;  Check:",
      bool(np.allclose(M50, np.column_stack([pi, pi]))))

# ── E. (e) Optional: power iteration & Markov (plots) ─────
print("\n── E. (e) Optional: convergence plots ──")


def power_iteration(Mat, num_iter=25, seed=42):
    """Power method: estimate of the dominant eigenvalue (Rayleigh quotient)."""
    rng = np.random.default_rng(seed)
    x = rng.normal(size=Mat.shape[0])
    x = x / np.linalg.norm(x)
    estimates = []
    for _ in range(num_iter):
        y = Mat @ x
        x = y / np.linalg.norm(y)
        estimates.append(float(x @ (Mat @ x)))   # Rayleigh quotient
    return x, estimates


v_est, history = power_iteration(A)
lam_max = float(np.max(vals))
lam_est = history[-1]
print(f"Dominant eigenvalue (power iteration, 25 steps): {lam_est:.10f}")
print(f"Exact value lam_max = {lam_max:.10f}"
      f"  | error = {abs(lam_est - lam_max):.2e}"
      f"  | convergence: {abs(lam_est - lam_max) < 1e-8}")

# Trajectory of the Markov chain from the state (1, 0)
state = np.array([1.0, 0.0])
traj = [state.copy()]
for _ in range(25):
    state = M @ state
    traj.append(state.copy())
traj = np.array(traj)
print(f"State after 25 steps: {np.round(traj[-1], 8)}"
      f"  | identical with pi: {bool(np.allclose(traj[-1], pi))}")

fig, axes = plt.subplots(1, 3, figsize=(14, 4.5))
fig.suptitle("Ch. 5 — Eigenvectors, Power Iteration, Markov",
             fontsize=13, fontweight='bold')

# (1) Eigenvectors of A in the plane
ax1 = axes[0]
ax1.set_title("Eigenvectors of $A$")
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

# (2) Convergence of power iteration
ax2 = axes[1]
ax2.set_title("Convergence of Power Iteration")
ax2.plot(range(1, len(history) + 1), history, 'o-', color='royalblue',
         lw=1.8, ms=3, label='Rayleigh quotient')
ax2.axhline(lam_max, color='tomato', ls='--', lw=1.5,
            label=f'$\\lambda_{{max}}={lam_max:.0f}$')
ax2.set_xlabel("Iteration"); ax2.set_ylabel("Estimate of $\\lambda$")
ax2.legend(fontsize=9); ax2.grid(True, alpha=0.3)

# (3) Convergence of the Markov chain to pi
ax3 = axes[2]
ax3.set_title("Markov chain → stationary $\\pi$")
ax3.plot(traj[:, 0], color='royalblue', lw=2, label='State 1')
ax3.plot(traj[:, 1], color='tomato', lw=2, label='State 2')
ax3.axhline(pi[0], color='royalblue', ls='--', lw=1, alpha=0.7)
ax3.axhline(pi[1], color='tomato', ls='--', lw=1, alpha=0.7)
ax3.text(14, pi[0] + 0.03, f'$\\pi_1={pi[0]:.1f}$', color='royalblue',
         fontsize=9)
ax3.text(14, pi[1] - 0.07, f'$\\pi_2={pi[1]:.1f}$', color='tomato',
         fontsize=9)
ax3.set_xlabel("Steps"); ax3.set_ylabel("Probability")
ax3.set_ylim(0, 1.05)
ax3.legend(fontsize=9); ax3.grid(True, alpha=0.3)

plt.tight_layout()
print("The convergence plots have been created.")
plt.show()
