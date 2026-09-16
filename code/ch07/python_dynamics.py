# ============================================================
# python_dynamics.py
# Chapter 7 — Dynamical Systems: Orbits and Phase Portraits
# Matzakos, N. (2026). Elements of Linear Algebra, Differential & Integral Calculus. NewTech Publications.
# ============================================================
#
# LIBRARIES:
#   numpy      -> matrices, eigenvalues, iterations
#   matplotlib -> orbits and phase portraits
#
# BASIC COMMANDS:
#   np.linalg.eigvals(A)  -> eigenvalues
#   A @ x                 -> matrix times vector
#   np.linalg.eig(P)      -> eigenvalues AND eigenvectors
#   matplotlib.pyplot     -> plots
# ============================================================

import numpy as np
import matplotlib.pyplot as plt

print("=" * 60)
print(" Chapter 7: Dynamical Systems — Orbits & Phase Portraits")
print("=" * 60)


def spectral_radius(M):
    """Spectral radius rho(M) = max |lam_i|."""
    return float(np.max(np.abs(np.linalg.eigvals(M))))


def stability_verdict(rho, tol=1e-12):
    """The conclusion FOLLOWS from the test — it is not fixed text."""
    if rho < 1 - tol:
        return ("rho < 1  ->  asymptotically STABLE: x_k -> 0")
    elif abs(rho - 1) <= tol:
        return ("rho = 1  ->  BORDERLINE case: the orbit stays bounded "
                "and converges to a NONZERO steady state, not to 0")
    else:
        return ("rho > 1  ->  UNSTABLE: the orbit moves away (|x_k| -> ∞)")


def trajectory(M, x0, steps):
    """Orbit x_{n+1} = M x_n, returns an array of shape (steps+1, 2)."""
    out = [np.asarray(x0, dtype=float)]
    for _ in range(steps):
        out.append(M @ out[-1])
    return np.array(out)


# ── A. (a) Orbit of 50 steps, eigenvalues and stability ──────
print("\n[A] Orbit x_{n+1} = A x_n and stability through rho(A)")

A  = np.array([[0.9, 0.1],
               [0.1, 0.9]])
x0 = np.array([1.0, 0.0])

evals = np.linalg.eigvals(A)
rhoA  = spectral_radius(A)
print("  A =", A.tolist())
print("  x0 =", x0.tolist())
print("  Eigenvalues:", np.round(np.real_if_close(evals), 10).tolist(),
      " (= [1.0 ; 0.8] ✓)")
print("  rho(A) =", round(rhoA, 12), " (= 1.0 ✓)")
print("  ", stability_verdict(rhoA))

traj = trajectory(A, x0, 50)
for k in range(1, 6):
    print(f"  x_{k} = {np.round(traj[k], 6).tolist()}")
print("  x_50 =", np.round(traj[50], 6).tolist(),
      " (-> [0.5 ; 0.5] ✓ — NOT to zero)")

# The sum x1+x2 is preserved, because (1,1) is a left
# eigenvector of A for lam = 1:  1^T A = 1^T.
print("  Conserved sum x1+x2:",
      np.round(traj[:, 0] + traj[:, 1], 10)[[0, 1, 25, 50]].tolist(),
      " (constant = 1 ✓)")
print("  Limit state theoretically = ((x1+x2)/2, (x1+x2)/2) = [0.5, 0.5] ✓")

# ── B. (b) Stationary distribution of a Markov chain, check P·pi = pi ──
print("\n[B] Markov chain: stationary distribution pi")

P = np.array([[0.9, 0.2],
              [0.1, 0.8]])
print("  P =", P.tolist(), " (columns summing to 1)")

vals, vecs = np.linalg.eig(P)
print("  Eigenvalues of P:", np.round(np.real_if_close(vals), 10).tolist(),
      " (= [1.0 ; 0.7] ✓)")

# We locate WHICH eigenvalue equals 1 — we do not assume a position.
i = int(np.argmin(np.abs(vals - 1.0)))
print("  lam = 1 is found at position:", i, " (lam =", round(float(np.real(vals[i])), 10), ")")

pi = np.real(vecs[:, i])
pi = pi / pi.sum()                      # normalization: sum equal to 1
print("  pi =", np.round(pi, 6).tolist(), " (= [2/3 ; 1/3] = [0.666667 ; 0.333333] ✓)")
print("  Check P·pi = pi :", bool(np.allclose(P @ pi, pi)), " (True ✓)")
print("  Check sum(pi_i) = 1 :", bool(np.isclose(pi.sum(), 1.0)), " (True ✓)")
print("  Error ||P·pi - pi||:", float(np.linalg.norm(P @ pi - pi)))

# ── C. (c) Orbit in state space and the components ───────────
print("\n[C] Plots: state space (x1,x2) and components x1(k), x2(k)")

fig1, ax = plt.subplots(1, 2, figsize=(10, 4))

ax[0].plot(traj[:, 0], traj[:, 1], 'o-', ms=3, lw=1, color='tab:blue',
           label='orbit')
ax[0].plot(traj[0, 0], traj[0, 1], 's', color='tab:green', ms=9, label='$x_0=(1,0)$')
ax[0].plot(traj[-1, 0], traj[-1, 1], '*', color='tab:red', ms=14,
           label='limit $(0.5\\,;\\,0.5)$')
ax[0].set_xlabel('$x_1$'); ax[0].set_ylabel('$x_2$')
ax[0].set_title('Orbit in state space  (rho(A)=1)')
ax[0].grid(alpha=.3); ax[0].legend(fontsize=8)

ax[1].plot(traj[:, 0], label='$x_1(k)$')
ax[1].plot(traj[:, 1], label='$x_2(k)$')
ax[1].axhline(0.5, color='k', ls='--', lw=.8, label='limit 0.5')
ax[1].set_xlabel('$k$'); ax[1].set_ylabel('value of the component')
ax[1].set_title('Components per step')
ax[1].grid(alpha=.3); ax[1].legend(fontsize=8)
fig1.tight_layout()

# ── D. (d) OPTIONAL: unstable system & comparison of portraits ─
print("\n[D] Optional: unstable system and comparison of phase portraits")

B = np.array([[1.1, 0.2],
              [0.1, 0.9]])
rhoB = spectral_radius(B)
print("  B =", B.tolist())
print("  Eigenvalues of B:", np.round(np.linalg.eigvals(B), 6).tolist(),
      " (= [1.173205 ; 0.826795] ✓)")
print("  rho(B) =", round(rhoB, 12), " (= 1.173205080757 ✓)")
print("  ", stability_verdict(rhoB))

trB = trajectory(B, x0, 20)
for k in (5, 10, 20):
    print(f"  B^{k} x0 = {np.round(trB[k], 6).tolist()}")
print("  ||x_20|| for A:", round(float(np.linalg.norm(traj[20])), 6),
      " | for B:", round(float(np.linalg.norm(trB[20])), 6),
      " (the second one much larger ✓)")

# A third, genuinely stable system for a complete comparison.
C = np.array([[0.8, 0.0],
              [0.0, 0.6]])
print("  C =", C.tolist(), " rho(C) =", round(spectral_radius(C), 12), " (= 0.8 ✓)")
print("  ", stability_verdict(spectral_radius(C)))

# Phase portraits: many initial conditions on the unit circle.
theta  = np.linspace(0, 2 * np.pi, 12, endpoint=False)
starts = np.stack([np.cos(theta), np.sin(theta)], axis=1)

fig2, axs = plt.subplots(1, 3, figsize=(13, 4.2))
for axi, (M, name, steps) in zip(
        axs,
        [(C, 'C: rho=0.8 < 1 — stable', 25),
         (A, 'A: rho=1 — borderline', 40),
         (B, 'B: rho=1.173 > 1 — unstable', 12)]):
    for s in starts:
        t = trajectory(M, s, steps)
        axi.plot(t[:, 0], t[:, 1], '-', lw=1, alpha=.85)
        axi.plot(t[0, 0], t[0, 1], '.', color='tab:green', ms=6)
        axi.plot(t[-1, 0], t[-1, 1], '.', color='tab:red', ms=6)
    axi.axhline(0, color='k', lw=.5); axi.axvline(0, color='k', lw=.5)
    axi.set_title(name, fontsize=10)
    axi.set_xlabel('$x_1$'); axi.set_ylabel('$x_2$')
    axi.set_aspect('equal', adjustable='datalim')
    axi.grid(alpha=.3)
fig2.suptitle('Phase portraits: green = start, red = end of the orbit',
              fontsize=10)
fig2.tight_layout()

print("\n  Comparison: for C the orbits collapse to 0; for A they converge")
print("  to the line x1 = x2 (the eigenspace of lam=1); for B they are")
print("  shot out along the eigenvector of lam = 1.1732.")

plt.show()
print("\n✓ Done.")
