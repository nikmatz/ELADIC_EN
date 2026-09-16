# ============================================================
# python_vectors.py
# Κεφάλαιο 1 — Γραμμικοί Διανυσματικοί Χώροι
# Ματζάκος, Ν. (2026). Στοιχεία Γραμμικής Άλγεβρας, Διαφορικού & Ολοκληρωτικού Λογισμού. NewTech Publications.
# ============================================================
#
# ΒΙΒΛΙΟΘΗΚΕΣ:
#   numpy    → γραμμική άλγεβρα (rank, det, SVD, null space)
#   scipy    → επιπλέον εργαλεία (null_space)
#   sympy    → ακριβείς υπολογισμοί (rref, GS συμβολικά)
#   matplotlib → οπτικοποίηση διανυσμάτων στο R²/R³
#
# ΒΑΣΙΚΕΣ ΕΝΤΟΛΕΣ:
#   np.linalg.det(A)        → ορίζουσα
#   np.linalg.matrix_rank(A)→ τάξη
#   np.linalg.svd(A)        → SVD ανάλυση
#   sympy.Matrix(A).rref()  → ανηγμένη κλιμακωτή (RREF)
#   sympy.Matrix(A).nullspace()  → μηδενόχωρος
#   sympy.Matrix(A).columnspace()→ χώρος στηλών
# ============================================================

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from sympy import Matrix, Rational, sqrt, symbols, pprint

print("=" * 55)
print(" Κεφάλαιο 1: Γραμμικοί Διανυσματικοί Χώροι — Python")
print("=" * 55)

# ── Α. Πίνακας, Ορίζουσα, Τάξη ───────────────────────────
print("\n── Α. Ανάλυση Πίνακα ──")

A = np.array([[1, 2, 1],
              [2, 1, 3],
              [1, 3, -1]], dtype=float)

print("Πίνακας A:")
print(A)
print(f"\ndet(A) = {np.linalg.det(A):.4f}")
print(f"rank(A) = {np.linalg.matrix_rank(A)}")

# ── Β. RREF και Χώροι (SymPy — ακριβής) ──────────────────
print("\n── Β. RREF & Χώροι (SymPy) ──")

A_sym = Matrix([[1, 2, 1],
                [2, 1, 3],
                [1, 3, -1]])

rref_A, pivots = A_sym.rref()
print("RREF(A):")
pprint(rref_A)
print(f"Pivot στήλες: {pivots}")

print("\nNull space (Μηδενόχωρος) — Ax=0:")
ns = A_sym.nullspace()
if ns:
    for i, v in enumerate(ns):
        print(f"  v{i+1} =", end=" ")
        pprint(v.T)
else:
    print("  Τετριμμένος (μηδέν) — A αντιστρέψιμος")

print("\nColumn space (Χώρος Στηλών):")
cs = A_sym.columnspace()
for i, v in enumerate(cs):
    print(f"  c{i+1} =", end=" ")
    pprint(v.T)

# ── Γ. Γραμμική Ανεξαρτησία ───────────────────────────────
print("\n── Γ. Γραμμική Ανεξαρτησία ──")

v1 = np.array([1, 0, 1])
v2 = np.array([0, 1, 1])
v3 = np.array([1, 1, 2])   # v3 = v1 + v2  → εξαρτημένα

M = np.column_stack([v1, v2, v3])
r = np.linalg.matrix_rank(M)

print(f"v₁ = {v1}")
print(f"v₂ = {v2}")
print(f"v₃ = {v3}  ← v₃ = v₁ + v₂")
print(f"\nrank([v₁|v₂|v₃]) = {r}")
print(f"→ rank = {r} < 3  ⇒  γραμμικά ΕΞΑΡΤΗΜΕΝΑ ✓")

# Ανεξάρτητα σύνολα
w1 = np.array([1, 1, 0])
w2 = np.array([1, 0, 1])
w3 = np.array([0, 1, 1])
N = np.column_stack([w1, w2, w3])
print(f"\nw₁={w1}, w₂={w2}, w₃={w3}")
print(f"rank([w₁|w₂|w₃]) = {np.linalg.matrix_rank(N)}")
print(f"→ rank = 3  ⇒  γραμμικά ΑΝΕΞΑΡΤΗΤΑ ✓")

# ── Δ. Gram-Schmidt Ορθοκανονικοποίηση ────────────────────
print("\n── Δ. Gram-Schmidt ──")

def gram_schmidt(vectors):
    """Gram-Schmidt ορθοκανονικοποίηση συνόλου διανυσμάτων."""
    orthonormal = []
    for v in vectors:
        w = v.copy().astype(float)
        for e in orthonormal:
            w -= np.dot(w, e) * e   # αφαιρούμε προβολή
        norm = np.linalg.norm(w)
        if norm > 1e-10:            # αν δεν είναι μηδέν
            orthonormal.append(w / norm)
    return orthonormal

basis = [w1.astype(float), w2.astype(float), w3.astype(float)]
ONB   = gram_schmidt(basis)

print("Αρχική βάση: w₁, w₂, w₃")
print("Ορθοκανονική βάση {e₁, e₂, e₃}:")
for i, e in enumerate(ONB):
    print(f"  e{i+1} = {np.round(e, 6)}")

# Επαλήθευση ορθογωνιότητας
print("\nΕπαλήθευση εσωτερικών γινομένων:")
print(f"  e₁·e₂ = {ONB[0] @ ONB[1]:.10f}  (≈ 0 ✓)")
print(f"  e₁·e₃ = {ONB[0] @ ONB[2]:.10f}  (≈ 0 ✓)")
print(f"  e₂·e₃ = {ONB[1] @ ONB[2]:.10f}  (≈ 0 ✓)")
print(f"  |e₁|  = {np.linalg.norm(ONB[0]):.6f}  (= 1 ✓)")

# Κατασκευή πίνακα Q και επαλήθευση Q·Qᵀ = I
Q = np.column_stack(ONB)
QQT = Q @ Q.T
print("\nQ·Qᵀ ≈ I₃:")
print(np.round(QQT, 8))
print("✓ Ορθοκανονικός πίνακας επαληθεύεται")

# ── Ε. Γραφική Απεικόνιση ──────────────────────────────────
print("\n── Ε. Γραφική Απεικόνιση ──")

fig = plt.figure(figsize=(13, 5))
fig.suptitle("Γραμμικοί Διανυσματικοί Χώροι — Διανύσματα στο ℝ³",
             fontsize=13, fontweight='bold')

# --- Αριστερά: Γραμμική εξάρτηση ---
ax1 = fig.add_subplot(121, projection='3d')
ax1.set_title("Γραμμική Εξάρτηση\n$v_3 = v_1 + v_2$")
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

# --- Δεξιά: Ορθοκανονική βάση Gram-Schmidt ---
ax2 = fig.add_subplot(122, projection='3d')
ax2.set_title("Ορθοκανονική Βάση (Gram-Schmidt)")
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
