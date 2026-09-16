# ============================================================
# python_linsys.py
# Κεφάλαιο 3 — Γραμμικά Συστήματα
# Ματζάκος, Ν. (2026). Στοιχεία Γραμμικής Άλγεβρας, Διαφορικού & Ολοκληρωτικού Λογισμού. NewTech Publications.
# ============================================================
#
# ΒΙΒΛΙΟΘΗΚΕΣ:
#   numpy         → αριθμητική επίλυση (solve, lstsq)
#   sympy         → RREF, ακριβής λύση, έλεγχος τύπου συστήματος
#   matplotlib    → γεωμετρική ερμηνεία (2D / 3D)
#
# ΒΑΣΙΚΕΣ ΕΝΤΟΛΕΣ:
#   np.linalg.solve(A, b)       → μοναδική λύση
#   np.linalg.lstsq(A, b)       → ελάχιστα τετράγωνα
#   np.linalg.matrix_rank(A)    → τάξη
#   sympy.Matrix.rref()         → ανηγμένη κλιμακωτή
#   sympy.linsolve()            → ακριβής λύση (άπειρες)
# ============================================================

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from sympy import Matrix, symbols, linsolve, Rational, pprint

print("=" * 55)
print(" Κεφάλαιο 3: Γραμμικά Συστήματα — Python")
print("=" * 55)

# ── Α. Σύστημα με Μοναδική Λύση ──────────────────────────
print("\n── Α. Μοναδική Λύση ──")
#  2x +  y -  z =  8
# -3x -  y + 2z = -11
#  -2x +  y + 2z = -3

A1 = np.array([[ 2,  1, -1],
               [-3, -1,  2],
               [-2,  1,  2]], dtype=float)
b1 = np.array([8, -11, -3], dtype=float)

x1 = np.linalg.solve(A1, b1)
print(f"Λύση: x={x1[0]:.4f}, y={x1[1]:.4f}, z={x1[2]:.4f}")
print(f"Επαλήθευση A@x = {np.round(A1 @ x1, 10)}  ✓")

# RREF με SymPy
Aug1 = Matrix([[ 2,  1, -1,  8],
               [-3, -1,  2, -11],
               [-2,  1,  2, -3]])
print("\nRREF([A|b]):")
pprint(Aug1.rref()[0])

# ── Β. Έλεγχος Τύπου Συστήματος (Θεώρημα Rouché–Capelli) ─
print("\n── Β. Ταξινόμηση Συστημάτων (Rouché–Capelli) ──")

def classify_system(A, b, label=""):
    """Ταξινομεί γραμμικό σύστημα σε μοναδική/άπειρες/ασύμβατο."""
    A_sym = Matrix(A.tolist())
    Aug   = A_sym.row_join(Matrix(b.reshape(-1,1).tolist()))
    rA    = A_sym.rank()
    rAug  = Aug.rank()
    n     = A.shape[1]
    if rA != rAug:
        result = "ΑΣΥΜΒΑΤΟ (0 λύσεις)"
    elif rA == n:
        result = "ΜΟΝΑΔΙΚΗ λύση"
    else:
        result = f"ΑΠΕΙΡΕΣ λύσεις  (ελεύθερες μεταβλητές: {n - rA})"
    print(f"  {label}: rank(A)={rA}, rank([A|b])={rAug}, n={n}  →  {result}")

# Μοναδική λύση
classify_system(A1, b1, "Σύστημα Α")

# Ασύμβατο
A2 = np.array([[1, 1], [2, 2]], dtype=float)
b2 = np.array([3, 5], dtype=float)
classify_system(A2, b2, "Σύστημα Β")

# Άπειρες λύσεις
A3 = np.array([[1, 2, -1], [2, 4, -2]], dtype=float)
b3 = np.array([3, 6], dtype=float)
classify_system(A3, b3, "Σύστημα Γ")

# ── Γ. Άπειρες Λύσεις — Παραμετρική Μορφή ────────────────
print("\n── Γ. Παραμετρική Λύση ──")
x, y, z = symbols('x y z')
sys3 = Matrix([[1, 2, -1, 3],
               [2, 4, -2, 6]])
rref3, pivots3 = sys3.rref()
print("RREF:"); pprint(rref3)
print(f"Pivots: {pivots3}  →  ελεύθερη μεταβλητή: y, z")

sol3 = linsolve((Matrix([[1,2,-1],[2,4,-2]]), Matrix([3,6])), x, y, z)
print("Παραμετρική λύση:"); pprint(sol3)

# ── Δ. Κανόνας Cramer ─────────────────────────────────────
print("\n── Δ. Κανόνας Cramer ──")
A_cr = np.array([[2, 1], [5, 3]], dtype=float)
b_cr = np.array([4, 7], dtype=float)
det_A = np.linalg.det(A_cr)
print(f"det(A) = {det_A:.4f}")

for i in range(2):
    Ai = A_cr.copy()
    Ai[:, i] = b_cr
    xi = np.linalg.det(Ai) / det_A
    print(f"  {'xy'[i]} = det(A{i+1})/det(A) = {np.linalg.det(Ai):.4f}/{det_A:.4f} = {xi:.4f}")

print(f"Επαλήθευση: {A_cr @ np.linalg.solve(A_cr, b_cr)} ≈ {b_cr}  ✓")

# ── Ε. Ομογενές Σύστημα ───────────────────────────────────
print("\n── Ε. Ομογενές Σύστημα Ax = 0 ──")
A5 = Matrix([[ 1, -2,  1],
             [ 2, -3,  1],
             [ 0,  1, -1]])
print(f"rank(A) = {A5.rank()}, nullity = {3 - A5.rank()}")
print("Μηδενόχωρος (μη τετριμμένες λύσεις):")
for v in A5.nullspace():
    pprint(v.T)

# ── Στ. Γεωμετρική Ερμηνεία (2D) ─────────────────────────
print("\n── Στ. Γεωμετρική Ερμηνεία ──")

fig, axes = plt.subplots(1, 3, figsize=(14, 4))
fig.suptitle("Γεωμετρική Ερμηνεία Γραμμικών Συστημάτων (2D)",
             fontsize=12, fontweight='bold')
t = np.linspace(-1, 6, 300)

# Μοναδική λύση: 2x+y=7, x+3y=11
ax = axes[0]; ax.set_title("Μοναδική Λύση\n$2x+y=7$,  $x+3y=11$")
ax.plot(t, 7 - 2*t, 'royalblue', lw=2, label='$2x+y=7$')
ax.plot(t, (11 - t)/3, 'tomato', lw=2, label='$x+3y=11$')
xs = np.linalg.solve([[2,1],[1,3]], [7,11])
ax.plot(*xs, 'ko', ms=8, zorder=5)
ax.annotate(f'({xs[0]:.1f},{xs[1]:.1f})', xs, xytext=(xs[0]+0.3, xs[1]+0.3), fontsize=9)
ax.set_xlim(-1,6); ax.set_ylim(-1,6); ax.grid(True,alpha=0.3)
ax.legend(fontsize=8); ax.set_xlabel('x'); ax.set_ylabel('y')

# Ασύμβατο: x+y=3, x+y=5
ax = axes[1]; ax.set_title("Ασύμβατο\n$x+y=3$,  $x+y=5$")
ax.plot(t, 3 - t, 'royalblue', lw=2, label='$x+y=3$')
ax.plot(t, 5 - t, 'tomato', lw=2, ls='--', label='$x+y=5$')
ax.set_xlim(-1,6); ax.set_ylim(-1,6); ax.grid(True,alpha=0.3)
ax.legend(fontsize=8); ax.set_xlabel('x'); ax.set_ylabel('y')
ax.text(2, 2.5, 'Παράλληλες\n(κανένα κοινό σημείο)', fontsize=8,
        ha='center', color='gray',
        bbox=dict(boxstyle='round', fc='white', alpha=0.8))

# Άπειρες: x+y=3, 2x+2y=6
ax = axes[2]; ax.set_title("Άπειρες Λύσεις\n$x+y=3$,  $2x+2y=6$")
ax.plot(t, 3 - t, 'royalblue', lw=3, label='$x+y=3$ (= $2x+2y=6$)')
ax.set_xlim(-1,6); ax.set_ylim(-1,6); ax.grid(True,alpha=0.3)
ax.legend(fontsize=8); ax.set_xlabel('x'); ax.set_ylabel('y')
ax.text(3, 1.5, 'Ταυτόσημες ευθείες\n(άπειρες λύσεις)', fontsize=8,
        ha='center', color='gray',
        bbox=dict(boxstyle='round', fc='white', alpha=0.8))

plt.tight_layout()
plt.show()

# ============================================================
# ΣΥΜΠΛΗΡΩΜΑ — Πίνακας Vandermonde & προσαρμογή πολυωνύμου
#   np.vander, np.polyfit, np.polyval
# ============================================================
import numpy as np

# Παρεμβολή: βρίσκουμε το πολυώνυμο 2ου βαθμού από 3 σημεία,
# λύνοντας το γραμμικό σύστημα V c = y με πίνακα Vandermonde.
xi = np.array([0.0, 1.0, 2.0])
yi = np.array([1.0, 3.0, 9.0])
V  = np.vander(xi, 3)          # στήλες: x^2, x^1, x^0
c  = np.linalg.solve(V, yi)    # συντελεστές (a, b, c) του ax^2+bx+c
print("Vandermonde V =\n", V)
print("Συντελεστές (από np.linalg.solve):", np.round(c, 6))

# Το ίδιο αποτέλεσμα με np.polyfit (ελάχιστα τετράγωνα):
c2 = np.polyfit(xi, yi, 2)
print("Συντελεστές (από np.polyfit)     :", np.round(c2, 6))

# Αποτίμηση του πολυωνύμου με np.polyval:
for x0 in (0.0, 1.0, 1.5, 2.0):
    print(f"  p({x0}) = {np.polyval(c, x0):.4f}")

# Υπερκαθορισμένο σύστημα (περισσότερα σημεία από αγνώστους):
xs = np.array([0., 1., 2., 3., 4.])
ys = np.array([1.1, 2.9, 9.2, 19.1, 32.8])
cls = np.polyfit(xs, ys, 2)    # βέλτιστη προσαρμογή κατά ελάχιστα τετράγωνα
print("Ελάχιστα τετράγωνα, βαθμός 2:", np.round(cls, 4))
print("Υπόλοιπα:", np.round(ys - np.polyval(cls, xs), 4))
