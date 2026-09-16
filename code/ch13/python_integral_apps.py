# ============================================================
# python_integral_apps.py
# Chapter 12 — Applications of Integral Calculus
# Matzakos, N. (2026). Elements of Linear Algebra, Differential & Integral Calculus. NewTech Publications.
# ============================================================
#
# LIBRARIES:
#   sympy              → exact values (area, volume, length)
#   scipy.integrate    → quad for numerical integration
#   numpy              → numerical processing
#   matplotlib         → 2D/3D visualization
#
# BASIC COMMANDS:
#   sympy.integrate(f, (x,a,b))    → area, volume
#   scipy.integrate.quad           → numerical
#   np.pi * integrate([f(x)]²)     → disk method
# ============================================================

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec
from mpl_toolkits.mplot3d import Axes3D
from sympy import (symbols, integrate, diff, sqrt, sin, cos,
                   log, pi, Abs, Rational, simplify, lambdify,
                   solve, tan, exp, pprint, oo)
from scipy.integrate import quad

x, y = symbols('x y', real=True)

print("=" * 55)
print(" Chapter 12: Applications of the Integral — Python")
print("=" * 55)

# ── A. Area of Plane Regions ────────────────────
print("\n── A. Area of Plane Regions ──")

# A1. |x³-x| on [-1,1]
A1_num, _ = quad(lambda t: abs(t**3 - t), -1, 1)
print(f"  ∫₋₁¹ |x³-x| dx ≈ {A1_num:.8f}  (theoretical = 1/2)")

# A2. |sinx-cosx| on [0,pi]
A2_num, _ = quad(lambda t: abs(np.sin(t)-np.cos(t)), 0, np.pi)
A2_sym = float(integrate(Abs(sin(x)-cos(x)), (x, 0, pi)))
print(f"  ∫₀^pi |sinx-cosx| dx = {A2_sym:.8f}")

# A3. Area between parabolas: y=-x²+4 and y=x²-2x
f_up3  = -x**2 + 4
f_dn3  =  x**2 - 2*x
xc3    = solve(f_up3 - f_dn3, x)
print(f"  Intersections: {xc3}")
A3     = integrate(f_up3 - f_dn3, (x, xc3[0], xc3[1]))
print(f"  Area between -x²+4 and x²-2x: {A3} = {float(A3):.6f}")

# ── B. Volume of Solids of Revolution ───────────────
print("\n── B. Volume of Solids of Revolution ──")

# Disk method: V = pi∫[f(x)]² dx
disk_cases = [
    (sqrt(x), 0, 4,    "y=√x about the x-axis, [0,4]"),
    (sin(x),  0, pi,   "y=sinx about the x-axis, [0,pi]"),
    (x**2,    0, 2,    "y=x² about the x-axis, [0,2]"),
]
print("  Disk Method (V = pi∫f²dx):")
for f_sym, a, b, label in disk_cases:
    V = pi * integrate(f_sym**2, (x, a, b))
    print(f"    {label}: V = {simplify(V)} ≈ {float(V):.6f}")

# Washer method: V = pi∫(R²-r²) dx
print("  Washer Method (V = pi∫(R²-r²)dx):")
R4, r4 = sqrt(x), x
V4 = pi * integrate(R4**2 - r4**2, (x, 0, 1))
print(f"    y=√x vs y=x about x, [0,1]: V = {V4} ≈ {float(V4):.6f}")

# Cylindrical shell method: V = 2pi∫x·f(x) dx
print("  Cylindrical Shell Method (V = 2pi∫x·f(x)dx):")
shell_cases = [
    (x**3, 0, 2, "y=x³ about the y-axis, [0,2]"),
    (sin(x), 0, pi, "y=sinx about the y-axis, [0,pi]"),
]
for f_sym, a, b, label in shell_cases:
    V = 2*pi * integrate(x*f_sym, (x, a, b))
    print(f"    {label}: V = {simplify(V)} ≈ {float(V):.6f}")

# ── C. Arc Length ────────────────────────────
print("\n── C. Arc Length (L = ∫√(1+[f']²)dx) ──")

arc_cases = [
    (x**Rational(3,2), 0, 4,    "y=x^(3/2) on [0,4]"),
    (log(cos(x)),      0, pi/3, "y=ln(cosx) on [0,pi/3]"),
    (x**2/2,           0, 2,    "y=x²/2 on [0,2]"),
]
for f_sym, a, b, label in arc_cases:
    fp_sym = diff(f_sym, x)
    integrand = sqrt(1 + fp_sym**2)
    try:
        L = integrate(integrand, (x, a, b))
        L_s = simplify(L)
        print(f"  {label}: L = {L_s} ≈ {float(L_s):.6f}")
    except Exception:
        L_num, _ = quad(lambdify(x, integrand, 'numpy'), float(a), float(b))
        print(f"  {label}: L ≈ {L_num:.6f} (numerically)")

# Numerical for the hard ones
L_circ, _ = quad(lambda t: np.sqrt(1 + (-t/np.sqrt(1-t**2+1e-14))**2),
                 -0.9999, 0.9999)
print(f"  Semicircle y=√(1-x²): L ≈ {L_circ:.6f}  (theoretical pi = {np.pi:.6f})")

# ── D. Area of a Surface of Revolution ───────────────
print("\n── D. Area of a Surface of Revolution (S = 2pi∫f√(1+f'²)dx) ──")

surf_cases = [
    (x,      0, 2,  "y=x (cone), [0,2]"),
    (sqrt(x),0, 3,  "y=√x, [0,3]"),
    (x**2,   0, 1,  "y=x², [0,1]"),
]
for f_sym, a, b, label in surf_cases:
    fp_sym = diff(f_sym, x)
    integrand = f_sym * sqrt(1 + fp_sym**2)
    try:
        S = 2*pi * integrate(integrand, (x, a, b))
        print(f"  {label}: S = {simplify(S)} ≈ {float(S):.6f}")
    except Exception:
        S_num, _ = quad(
            lambda t: 2*np.pi * float(lambdify(x, f_sym, 'numpy')(t))
                      * np.sqrt(1 + float(lambdify(x, fp_sym, 'numpy')(t))**2),
            float(a), float(b))
        print(f"  {label}: S ≈ {S_num:.6f} (numerically)")

# ── E. Physical Applications ─────────────────────
print("\n── E. Physical Applications ──")

# E1. Work done on a spring
k = 200  # N/m
W = float(integrate(k*x, (x, 0, Rational(1,10))))
print(f"  Work of the spring (k={k} N/m, x in [0,0.1m]): W = {W} J")

# E2. Centroid
f_bar = x**2
a_bar, b_bar = 0, 3
xbar = float(integrate(x*f_bar, (x, a_bar, b_bar)) /
             integrate(f_bar,   (x, a_bar, b_bar)))
print(f"  Centroid of y=x², [0,3]: x̄ = {xbar:.4f}")

# E3. Hydrostatic force F = rho·g ∫y·w(y) dy
# Rectangular tank of width 4 m, rho·g=9810 N/m³, depth [0,3]
rho_g = 9810
F_hydro = float(rho_g * integrate(y * 4, (y, 0, 3)))
print(f"  Hydrostatic force (4m×3m): F = {F_hydro:.0f} N = {F_hydro/1000:.1f} kN")

# ── F. Plots ───────────────────────────────
print("\n── F. Plots ──")

fig = plt.figure(figsize=(14, 9))
fig.suptitle("Applications of Integral Calculus", fontsize=13, fontweight='bold')
gs = gridspec.GridSpec(2, 3, fig, hspace=0.45, wspace=0.35)

# 1. Area |x³-x|
ax1 = fig.add_subplot(gs[0, 0])
t1  = np.linspace(-1.3, 1.3, 400)
y1  = t1**3 - t1
ax1.plot(t1, y1, 'royalblue', lw=2.5, label=r'$f(x)=x^3-x$')
tx1p = np.linspace(0, 1, 200)
tx1m = np.linspace(-1, 0, 200)
ax1.fill_between(tx1p, tx1p**3-tx1p, alpha=0.3, color='green')
ax1.fill_between(tx1m, tx1m**3-tx1m, alpha=0.3, color='tomato')
ax1.axhline(0, color='k', lw=0.8)
ax1.set_title(r"$\int_{-1}^{1}|x^3-x|\,dx$", fontsize=10)
ax1.legend(fontsize=8); ax1.grid(True, alpha=0.3)

# 2. Area between parabolas
ax2 = fig.add_subplot(gs[0, 1])
t2  = np.linspace(-1.5, 2.5, 400)
ax2.plot(t2, -t2**2+4,   'royalblue', lw=2.5, label=r'$y=-x^2+4$')
ax2.plot(t2,  t2**2-2*t2,'tomato',    lw=2.5, label=r'$y=x^2-2x$')
tx2 = np.linspace(-1, 2, 200)
ax2.fill_between(tx2, tx2**2-2*tx2, -tx2**2+4, alpha=0.25, color='green',
                  label='A=9')
ax2.axhline(0, color='k', lw=0.5)
ax2.set_ylim(-3, 6)
ax2.set_title("Area between two parabolas", fontsize=10)
ax2.legend(fontsize=8); ax2.grid(True, alpha=0.3)

# 3. Solid of revolution: y=√x, [0,4] about the x-axis
ax3 = fig.add_subplot(gs[0, 2], projection='3d')
theta = np.linspace(0, 2*np.pi, 60)
xv    = np.linspace(0, 4, 60)
X3, T3 = np.meshgrid(xv, theta)
R3 = np.sqrt(X3)
Y3 = R3 * np.cos(T3)
Z3 = R3 * np.sin(T3)
ax3.plot_surface(X3, Y3, Z3, alpha=0.6, cmap='Blues')
ax3.set_xlabel('x'); ax3.set_ylabel('y'); ax3.set_zlabel('z')
ax3.set_title(r"$y=\sqrt{x}$ about the $x$-axis", fontsize=9)

# 4. Arc length y=x^(3/2)
ax4 = fig.add_subplot(gs[1, 0])
t4  = np.linspace(0, 4, 400)
y4  = t4**1.5
ax4.plot(t4, y4, 'royalblue', lw=2.5, label=r'$y=x^{3/2}$')
# Cumulative length
from scipy.integrate import cumulative_trapezoid
s4 = cumulative_trapezoid(np.sqrt(1 + (1.5*t4**0.5)**2), t4, initial=0)
ax4_twin = ax4.twinx()
ax4_twin.plot(t4, s4, 'tomato', lw=1.8, ls='--', label='L(t) (cumulative)')
ax4_twin.set_ylabel('Arc length L', color='tomato', fontsize=8)
ax4.set_title(r"Arc length $y=x^{3/2}$", fontsize=10)
ax4.legend(loc='upper left', fontsize=8)
ax4_twin.legend(loc='lower right', fontsize=8)
ax4.grid(True, alpha=0.3)

# 5. Work done on a spring
ax5 = fig.add_subplot(gs[1, 1])
xv5 = np.linspace(0, 0.1, 200)
Fv5 = 200 * xv5
ax5.plot(xv5*100, Fv5, 'royalblue', lw=2.5, label='F(x)=200x')
ax5.fill_between(xv5*100, Fv5, alpha=0.25, color='royalblue',
                  label=f'W={W:.1f} J')
ax5.set_xlabel('Extension x (cm)')
ax5.set_ylabel('Force F (N)')
ax5.set_title("Work of a Spring (k=200 N/m)", fontsize=10)
ax5.legend(fontsize=9); ax5.grid(True, alpha=0.3)

# 6. Centroid
ax6 = fig.add_subplot(gs[1, 2])
t6  = np.linspace(0, 3, 400)
y6  = t6**2
ax6.plot(t6, y6, 'royalblue', lw=2.5, label=r'$f(x)=x^2$')
ax6.fill_between(t6, y6, alpha=0.2, color='royalblue')
ax6.axvline(xbar, color='tomato', ls='--', lw=2,
            label=f'$\\bar{{x}}={xbar:.2f}$')
ax6.set_title(r"Centroid $y=x^2,\ [0,3]$", fontsize=10)
ax6.legend(fontsize=9); ax6.grid(True, alpha=0.3)

plt.savefig("integral_applications.png", dpi=120, bbox_inches='tight')
print("Plot saved: integral_applications.png")
plt.show()
