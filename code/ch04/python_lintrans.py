# ============================================================
# python_lintrans.py
# Κεφάλαιο 4 — Γραμμικοί Μετασχηματισμοί
# Ματζάκος, Ν. (2026). Στοιχεία Γραμμικής Άλγεβρας, Διαφορικού & Ολοκληρωτικού Λογισμού. NewTech Publications.
# ============================================================
#
# ΒΙΒΛΙΟΘΗΚΕΣ:
#   numpy      → εφαρμογή μετασχηματισμών (@ operator)
#   sympy      → πυρήνας, εικόνα, ακριβής λύση
#   matplotlib → γεωμετρική οπτικοποίηση (μοναδιαίος κύκλος,
#                μετασχηματισμός πολυγώνων)
#
# ΒΑΣΙΚΕΣ ΕΝΤΟΛΕΣ:
#   A @ v                    → T(v) = εφαρμογή μετασχηματισμού
#   A @ B                    → σύνθεση T₂∘T₁
#   np.linalg.inv(A)         → αντίστροφος μετασχηματισμός
#   sympy.Matrix.nullspace() → πυρήνας
#   sympy.Matrix.columnspace()→ εικόνα
#   np.linalg.det(A)         → det (αντιστρεψιμότητα, εμβαδόν)
# ============================================================

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.patches import FancyArrowPatch
from sympy import Matrix, pi, cos, sin, sqrt, Rational, pprint

print("=" * 55)
print(" Κεφάλαιο 4: Γραμμικοί Μετασχηματισμοί — Python")
print("=" * 55)

# ── Α. Ορισμός & Εφαρμογή Μετασχηματισμού ────────────────
print("\n── Α. Μετασχηματισμός T: ℝ³ → ℝ³ ──")

A = np.array([[ 1,  2,  0],
              [ 3, -1,  1],
              [ 0,  2, -1]], dtype=float)

print("A =\n", A)

# Εφαρμογή σε βασικά διανύσματα
e1, e2, e3 = np.eye(3)
print(f"\nT(e₁) = {A @ e1}")
print(f"T(e₂) = {A @ e2}")
print(f"T(e₃) = {A @ e3}")

u = np.array([2, -1, 3])
print(f"\nT([2,-1,3]ᵀ) = {A @ u}")

# Έλεγχος γραμμικότητας
w = np.array([1, 1, 1])
alpha, beta = 2, -1
lhs = A @ (alpha*u + beta*w)
rhs = alpha*(A @ u) + beta*(A @ w)
print(f"\nΈλεγχος: T(2u-w) = {lhs}")
print(f"         2T(u)-T(w) = {rhs}")
print(f"Ισότητα: {np.allclose(lhs, rhs)}  ✓")

# ── Β. Πυρήνας (Kernel) & Εικόνα (Image) ─────────────────
print("\n── Β. Ker(T) & Im(T) ──")

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
    print("  {0}  (μόνο το μηδενικό διάνυσμα)")

print("\nIm(T) — βάση:")
for v in A_sym.columnspace(): pprint(v.T)

# ── Γ. Γεωμετρικοί Μετασχηματισμοί στο ℝ² ───────────────
print("\n── Γ. Γεωμετρικοί Μετασχηματισμοί ──")

def rot(theta_deg):
    """Πίνακας στροφής κατά θ μοίρες."""
    t = np.radians(theta_deg)
    return np.array([[np.cos(t), -np.sin(t)],
                     [np.sin(t),  np.cos(t)]])

def ref_x():
    return np.array([[1, 0], [0, -1]])

def scale(sx, sy):
    return np.array([[sx, 0], [0, sy]])

def shear(k):
    """Διάτμηση ως προς x."""
    return np.array([[1, k], [0, 1]])

R45  = rot(45)
R90  = rot(90)
Refx = ref_x()
Sc   = scale(2, 0.5)
Sh   = shear(1)

print(f"R₄₅·(1,0)ᵀ = {np.round(R45 @ [1,0], 6)}")
print(f"  (= (√2/2, √2/2) ≈ (0.7071, 0.7071) ✓)")
print(f"det(R₄₅) = {np.linalg.det(R45):.6f}  (= 1 → διατηρεί εμβαδόν ✓)")
print(f"det(Ref_x) = {np.linalg.det(Refx):.1f}  (= -1 → αντιστρέφει προσανατολισμό)")
print(f"det(Scale(2,0.5)) = {np.linalg.det(Sc):.4f}  (= 2·0.5 = 1)")

# Σύνθεση: μη αντιμεταθετική
print(f"\nR₉₀∘Ref_x =\n{np.round(R90 @ Refx, 6)}")
print(f"Ref_x∘R₉₀ =\n{np.round(Refx @ R90, 6)}")
print("Διαφορετικά!  →  μη αντιμεταθετικότητα ✓")

# ── Δ. Γραφική Απεικόνιση ──────────────────────────────────
print("\n── Δ. Γραφική Απεικόνιση ──")

# Τετράγωνο μοναδιαίας πλευράς (+ κλειστό)
sq = np.array([[0,1,1,0,0],
               [0,0,1,1,0]], dtype=float)

fig, axes = plt.subplots(2, 3, figsize=(13, 8))
fig.suptitle("Γεωμετρικοί Γραμμικοί Μετασχηματισμοί", fontsize=13, fontweight='bold')

transforms = [
    (np.eye(2),  "Ταυτοτικός $I$"),
    (R45,        "Στροφή $45°$"),
    (R90,        "Στροφή $90°$"),
    (Refx,       "Ανάκλαση ως προς $x$"),
    (Sc,         "Κλιμάκωση\n$s_x=2, s_y=0.5$"),
    (Sh,         "Διάτμηση $k=1$"),
]

for ax, (T, title) in zip(axes.flat, transforms):
    sq_t = T @ sq
    ax.fill(sq[0], sq[1], alpha=0.25, color='royalblue', label='Αρχικό')
    ax.fill(sq_t[0], sq_t[1], alpha=0.35, color='tomato', label='Μετά T')
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
