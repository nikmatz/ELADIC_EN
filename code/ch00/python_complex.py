# ============================================================
# python_complex.py
# Κεφάλαιο 0 — Μαθηματικό Υπόβαθρο: Μιγαδικοί Αριθμοί
# Ματζάκος, Ν. (2026). Στοιχεία Γραμμικής Άλγεβρας, Διαφορικού & Ολοκληρωτικού Λογισμού. NewTech Publications.
# ============================================================
#
# ΒΙΒΛΙΟΘΗΚΕΣ:
#   cmath    → αριθμητικοί υπολογισμοί με μιγαδικούς
#   sympy    → συμβολικοί υπολογισμοί (ακριβείς)
#   numpy    → αριθμητικές πράξεις πινάκων
#   matplotlib → γραφικές παραστάσεις (Argand diagram)
#
# ΒΑΣΙΚΕΣ ΕΝΤΟΛΕΣ:
#   cmath.polar(z)      → (r, θ)  πολικές συντεταγμένες
#   cmath.rect(r, θ)    → z = r·e^(iθ)  ορθογώνιες
#   cmath.sqrt(z)       → τετραγωνική ρίζα
#   cmath.phase(z)      → γωνία arg(z) σε [-π, π]
#   sympy.simplify(expr)→ συμβολική απλοποίηση
#   sympy.solve(eq, x)  → επίλυση εξίσωσης
# ============================================================

import cmath
import math
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from sympy import (symbols, I, pi, sqrt, exp, cos, sin,
                   simplify, expand, conjugate, solve,
                   re, im, Abs, arg,
                   N, Rational, pretty_print as pprint)

print("=" * 55)
print(" Κεφάλαιο 0: Μιγαδικοί Αριθμοί — Python")
print("=" * 55)

# ── Α. Βασικές Πράξεις (cmath — αριθμητικό) ──────────────
print("\n── Α. Βασικές Πράξεις (cmath) ──")

z1 = 3 + 4j       # z₁ = 3 + 4i
z2 = 1 - 2j       # z₂ = 1 - 2i

print(f"z₁ = {z1}    z₂ = {z2}")
print(f"z₁ + z₂ = {z1 + z2}")
print(f"z₁ - z₂ = {z1 - z2}")
print(f"z₁ · z₂ = {z1 * z2}")
print(f"z₁ / z₂ = {z1 / z2:.4f}")

r1, theta1 = cmath.polar(z1)
print(f"\n|z₁| = {r1:.4f}  (= √(3²+4²) = 5 ✓)")
print(f"arg(z₁) = {theta1:.4f} rad = {math.degrees(theta1):.2f}°")

# Επαλήθευση: z · conj(z) = |z|²
print(f"z₁ · conj(z₁) = {z1 * z1.conjugate():.1f}  (= |z₁|² = 25 ✓)")

# ── Β. Φάσορες AC — Εκθετική Μορφή ───────────────────────
print("\n── Β. Φάσορες AC — Εκθετική Μορφή ──")

zA = cmath.rect(5, math.pi / 3)   # 5·e^(iπ/3),  |zA|=5, θ=60°
zB = cmath.rect(2, math.pi / 6)   # 2·e^(iπ/6),  |zB|=2, θ=30°

print(f"z_A = 5·e^(iπ/3) = {zA.real:.4f} + {zA.imag:.4f}i")
print(f"z_B = 2·e^(iπ/6) = {zB.real:.4f} + {zB.imag:.4f}i")

prod = zA * zB
print(f"\nz_A · z_B = {prod:.4f}")
print(f"  Μέτρο:  {abs(prod):.4f}  (= 5·2 = 10 ✓)")
print(f"  Γωνία:  {math.degrees(cmath.phase(prod)):.1f}°  (= 60°+30° = 90° ✓)")

quot = zA / zB
print(f"\nz_A / z_B = {quot.real:.4f} + {quot.imag:.4f}i")
print(f"  Μέτρο:  {abs(quot):.4f}  (= 5/2 = 2.5 ✓)")
print(f"  Γωνία:  {math.degrees(cmath.phase(quot)):.1f}°  (= 60°-30° = 30° ✓)")

# ── Γ. Θεώρημα De Moivre ──────────────────────────────────
print("\n── Γ. Θεώρημα De Moivre ──")
# (r·e^(iθ))^n = r^n · e^(inθ)

base = cmath.rect(5, math.pi / 3)   # 5·e^(iπ/3)
z_cubed = base ** 3
print(f"(5·e^(iπ/3))³ = {z_cubed:.6f}")
print(f"  Μέτρο:  {abs(z_cubed):.1f}  (= 5³ = 125 ✓)")
print(f"  Γωνία:  {math.degrees(cmath.phase(z_cubed)):.1f}°  (= 3·60° = 180° ✓)")
print(f"  Άρα:    = -125  (= 125·(cos180° + i·sin180°) ✓)")

# Επαλήθευση De Moivre με SymPy (συμβολικά)
theta_s = pi / 3
z_sym   = cos(theta_s) + I * sin(theta_s)
z_sym_3 = simplify(expand(z_sym**3))
expected = cos(3 * theta_s) + I * sin(3 * theta_s)
print(f"\nΕπαλήθευση (SymPy):")
print(f"  (cosθ + i·sinθ)³ - (cos3θ + i·sin3θ) = {simplify(z_sym_3 - expected)}")
print(f"  (= 0, άρα De Moivre ✓)")

# ── Δ. Ρίζες Μιγαδικών Αριθμών ───────────────────────────
print("\n── Δ. Ρίζες Μιγαδικών Αριθμών ──")

def complex_roots(w, n):
    """Βρίσκει όλες τις n-ιοστές ρίζες του w = r·e^(iθ)."""
    r, theta = cmath.polar(w)
    roots = []
    for k in range(n):
        r_k     = r ** (1 / n)
        theta_k = (theta + 2 * math.pi * k) / n
        roots.append(cmath.rect(r_k, theta_k))
    return roots

# Τετραγωνικές ρίζες του -1
print("Ρίζες x² = -1:")
for k, root in enumerate(complex_roots(-1, 2)):
    print(f"  x_{k} = {root:.4f}  (επαλήθευση: x²={root**2:.1f} ✓)")

# Τετραγωνικές ρίζες του 1+i
w = 1 + 1j
print(f"\nΡίζες x² = 1+i:")
for k, root in enumerate(complex_roots(w, 2)):
    print(f"  x_{k} = {root:.4f}  (επαλήθευση: x²={root**2:.4f} ✓)")

# Κυβικές ρίζες του 8
print(f"\nΡίζες x³ = 8:")
for k, root in enumerate(complex_roots(8, 3)):
    print(f"  x_{k} = {root.real:.4f} + {root.imag:.4f}i  (επαλήθευση: x³={root**3:.2f})")

# ── Ε. Γραφική Απεικόνιση — Διάγραμμα Argand ─────────────
print("\n── Ε. Γραφική Απεικόνιση ──")

fig, axes = plt.subplots(1, 2, figsize=(12, 5))
fig.suptitle("Μιγαδικοί Αριθμοί — Διάγραμμα Argand", fontsize=13, fontweight='bold')

# --- Αριστερά: βασικές πράξεις ---
ax1 = axes[0]
ax1.set_title("Βασικές Πράξεις")
points = {'$z_1=3+4i$': z1, '$z_2=1-2i$': z2,
          '$z_1+z_2$': z1+z2, '$z_1·z_2$': z1*z2}
colors  = ['royalblue', 'tomato', 'forestgreen', 'darkorchid']
for (lbl, z), col in zip(points.items(), colors):
    ax1.annotate('', xy=(z.real, z.imag), xytext=(0, 0),
                 arrowprops=dict(arrowstyle='->', color=col, lw=1.8))
    ax1.plot(z.real, z.imag, 'o', color=col, ms=7)
    ax1.annotate(lbl, (z.real, z.imag), textcoords="offset points",
                 xytext=(6, 6), fontsize=9, color=col)
ax1.axhline(0, color='k', lw=0.5); ax1.axvline(0, color='k', lw=0.5)
ax1.grid(True, alpha=0.3); ax1.set_aspect('equal')
ax1.set_xlabel("Πραγματικός άξονας"); ax1.set_ylabel("Φανταστικός άξονας")

# --- Δεξιά: ρίζες z³=8 στον μοναδιαίο κύκλο ×2 ---
ax2 = axes[1]
ax2.set_title("Κυβικές ρίζες x³ = 8")
roots_8 = complex_roots(8, 3)
theta_plot = np.linspace(0, 2*np.pi, 300)
ax2.plot(2*np.cos(theta_plot), 2*np.sin(theta_plot), 'k--', lw=0.8, alpha=0.4,
         label='Κύκλος r=2')
for k, root in enumerate(roots_8):
    ax2.plot(root.real, root.imag, 'o', ms=10, label=f'$x_{k}$')
    ax2.annotate(f'$x_{k}$', (root.real, root.imag),
                 textcoords="offset points", xytext=(8, 5), fontsize=11)
ax2.axhline(0, color='k', lw=0.5); ax2.axvline(0, color='k', lw=0.5)
ax2.grid(True, alpha=0.3); ax2.set_aspect('equal')
ax2.legend(fontsize=9)
ax2.set_xlabel("Πραγματικός άξονας"); ax2.set_ylabel("Φανταστικός άξονας")

plt.tight_layout()
plt.show()
