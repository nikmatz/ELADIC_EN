# ============================================================
# python_efarm_ol.py
# Chapter 17 — Applications of Integral Calculus
#   Area, Volume of Revolution, Arc Length, Physical Applications
# Matzakos, N. (2026). Elements of Linear Algebra, Differential & Integral Calculus. NewTech Publications.
# ------------------------------------------------------------
# BASIC COMMANDS:
#   sympy.integrate(f, (x,a,b))   -> definite integral
#   sympy.diff(f, x)              -> derivative
#   sympy.solve(f-g, x)           -> points of intersection
#   scipy.integrate.quad(f, a, b) -> numerical integral
#   matplotlib.fill_between()     -> shaded region
#   mpl_toolkits.mplot3d          -> 3D solid of revolution
# ============================================================
import sympy as sp
import numpy as np
import matplotlib.pyplot as plt
from scipy.integrate import quad, cumulative_trapezoid
from mpl_toolkits.mplot3d import Axes3D          # noqa: F401 (enables 3D)

x = sp.symbols('x', real=True)
y = sp.symbols('y', nonnegative=True)

print("=" * 62)
print(" Chapter 17: Applications of Integral Calculus")
print("=" * 62)


# ============================================================
# A. AREA BETWEEN CURVES
# ============================================================
print("\n=== A. AREA ===")

# A1.  int_{-1}^{1} |x^3 - x| dx
f_abs = sp.Abs(x**3 - x)
A1 = sp.integrate(f_abs, (x, -1, 1))
A1_num, A1_err = quad(lambda t: abs(t**3 - t), -1, 1)
print(f"\nA1. ∫_(-1)^1 |x^3-x| dx = {A1} = {float(A1)}   (expected 1/2)")
print(f"    scipy quad            = {A1_num:.12f}  (est. error {A1_err:.1e})")
print(f"    |difference| < 1e-8   : {abs(float(A1) - A1_num) < 1e-8}")

# A2.  Area between y = -x^2+4 and y = x^2-2x
f = -x**2 + 4
g = x**2 - 2*x
# ALWAYS sort the roots, otherwise the area comes out negative.
tomes = sorted(sp.solve(sp.Eq(f, g), x))
a, b = tomes[0], tomes[1]
A2 = sp.integrate(f - g, (x, a, b))
print(f"\nA2. f(x) = {f},  g(x) = {g}")
print(f"    intersections (sorted): x = {a}, x = {b}   (expected -1, 2)")
print(f"    Area = ∫_({a})^({b}) (f-g) dx = {A2}   (expected 9)")
print(f"    positive area         : {A2 > 0}")

xv = np.linspace(float(a) - 0.8, float(b) + 0.8, 400)
fv = -xv**2 + 4
gv = xv**2 - 2*xv
xs = np.linspace(float(a), float(b), 300)
fs_ = -xs**2 + 4
gs_ = xs**2 - 2*xs

plt.figure(figsize=(7, 4.4))
plt.plot(xv, fv, 'b-', lw=2, label=r'$f(x)=-x^2+4$')
plt.plot(xv, gv, 'r-', lw=2, label=r'$g(x)=x^2-2x$')
plt.fill_between(xs, gs_, fs_, alpha=0.30, color='tab:green',
                 label=f'Area = {A2}')
plt.plot([float(a), float(b)], [float(f.subs(x, a)), float(f.subs(x, b))],
         'ko', ms=5)
plt.axhline(0, color='k', lw=0.6)
plt.xlabel('x'); plt.ylabel('y')
plt.title('A. Area between two curves')
plt.legend(); plt.grid(True, alpha=0.3)
plt.tight_layout()


# ============================================================
# B. VOLUME OF REVOLUTION — all three methods on the SAME solid
#    Region between y = sqrt(x) (outer) and y = x (inner),
#    revolved about the x-axis. Intersections: x = 0, 1.
# ============================================================
print("\n=== B. VOLUME OF REVOLUTION ===")

R_ex = sp.sqrt(x)      # outer radius
r_es = x               # inner radius
tomesB = sorted(sp.solve(sp.Eq(x, x**2), x))     # sqrt(x)=x <=> x=x^2, x>=0
print(f"\nRegion: y = sqrt(x) and y = x,  intersections x = {tomesB}   (expected [0, 1])")

# (i) DISKS: the volume as the difference of two solid bodies
V_disk_ex = sp.pi * sp.integrate(R_ex**2, (x, 0, 1))
V_disk_es = sp.pi * sp.integrate(r_es**2, (x, 0, 1))
V_disks = sp.simplify(V_disk_ex - V_disk_es)
# (ii) WASHERS: V = pi*∫ (R^2 - r^2) dx
V_wash = sp.simplify(sp.pi * sp.integrate(R_ex**2 - r_es**2, (x, 0, 1)))
# (iii) SHELLS with respect to y: radius y, height (x_right - x_left) = y - y^2
V_shell = sp.simplify(2*sp.pi * sp.integrate(y*(y - y**2), (y, 0, 1)))

print(f"  (i)   disks     : pi∫x dx - pi∫x² dx = {V_disk_ex} - {V_disk_es} = {V_disks}")
print(f"  (ii)  washers   : pi∫(R²-r²) dx                    = {V_wash}")
print(f"  (iii) shells    : 2pi∫y(y-y²) dy                    = {V_shell}")
print(f"  numerically: {float(V_wash):.12f}   (expected pi/6 = {float(sp.pi/6):.12f})")
print(f"  disks == washers    : {sp.simplify(V_disks - V_wash) == 0}")
print(f"  washers == shells   : {sp.simplify(V_wash - V_shell) == 0}")
print(f"  all three equal to pi/6  : "
      f"{sp.simplify(V_disks - sp.pi/6) == 0 and sp.simplify(V_shell - sp.pi/6) == 0}")

# The remaining cases from the Maxima activity
V_sqrt = sp.pi * sp.integrate(x, (x, 0, 4))                 # disks, y=sqrt(x), [0,4]
V_sin = sp.pi * sp.integrate(sp.sin(x)**2, (x, 0, sp.pi))   # disks, y=sin x, [0,pi]
V_x3 = 2*sp.pi * sp.integrate(x*x**3, (x, 0, 2))            # shells, y=x^3, [0,2]
print(f"\n  disks   y=sqrt(x), [0,4] : V = {V_sqrt}  (expected 8pi)")
print(f"  disks   y=sin(x), [0,pi] : V = {V_sin}  (expected pi²/2)")
print(f"  shells  y=x³ about y, [0,2]: V = {V_x3}  (expected 64pi/5)")
print(f"  checks: {sp.simplify(V_sqrt-8*sp.pi)==0}, "
      f"{sp.simplify(V_sin-sp.pi**2/2)==0}, {sp.simplify(V_x3-sp.Rational(64,5)*sp.pi)==0}")

# --- 3D visualization of the solid (annular) ---
tt = np.linspace(0, 1, 60)
th = np.linspace(0, 2*np.pi, 60)
T, TH = np.meshgrid(tt, th)
fig = plt.figure(figsize=(7, 5))
ax = fig.add_subplot(111, projection='3d')
# outer surface: radius sqrt(x)
ax.plot_surface(T, np.sqrt(T)*np.cos(TH), np.sqrt(T)*np.sin(TH),
                color='tab:blue', alpha=0.45, linewidth=0)
# inner surface: radius x
ax.plot_surface(T, T*np.cos(TH), T*np.sin(TH),
                color='tab:red', alpha=0.75, linewidth=0)
ax.set_xlabel('x'); ax.set_ylabel('y'); ax.set_zlabel('z')
ax.set_title('B. Solid of revolution: y=√x (outer) and y=x (inner), V = pi/6')
plt.tight_layout()


# ============================================================
# C. ARC LENGTH:  L = ∫_a^b sqrt(1 + f'(x)^2) dx
# ============================================================
print("\n=== C. ARC LENGTH ===")

# C1.  y = x^(3/2) on [0,4]
y1 = x**sp.Rational(3, 2)
ds1 = sp.sqrt(1 + sp.diff(y1, x)**2)
L1 = sp.simplify(sp.integrate(ds1, (x, 0, 4)))
L1_num, L1_err = quad(sp.lambdify(x, ds1, 'numpy'), 0, 4)
L1_kleisto = (80*sp.sqrt(10) - 8) / 27
print(f"\nC1. y = x^(3/2), [0,4]")
print(f"    f'(x) = {sp.diff(y1, x)},  sqrt(1+f'^2) = {sp.simplify(ds1)}")
print(f"    L (sympy) = {L1} = {float(L1):.12f}   (expected (80√10-8)/27 = 9.073415289388)")
print(f"    L (quad)  = {L1_num:.12f}  (est. error {L1_err:.1e})")
print(f"    closed form correct : {sp.simplify(L1 - L1_kleisto) == 0}")
print(f"    |sympy - quad| < 1e-8: {abs(float(L1) - L1_num) < 1e-8}")

# C2.  y = ln(cos x) on [0, pi/3]  ->  sqrt(1+tan²x) = sec x
y2 = sp.log(sp.cos(x))
d2 = sp.diff(y2, x)
ds2 = sp.sqrt(sp.trigsimp(1 + d2**2))
L2 = sp.simplify(sp.integrate(sp.sec(x), (x, 0, sp.pi/3)))
L2_num, L2_err = quad(lambda t: 1/np.cos(t), 0, np.pi/3)
print(f"\nC2. y = ln(cos x), [0, pi/3]")
print(f"    f'(x) = {sp.simplify(d2)},  trigsimp(1+f'^2) = {sp.trigsimp(1 + d2**2)}")
print(f"    L (sympy) = {float(L2):.12f}   (expected ln(2+√3) = 1.316957896925)")
print(f"    L (quad)  = {L2_num:.12f}  (est. error {L2_err:.1e})")
# SymPy returns the logarithm in a different (equivalent) form, so
# we check the equivalent statement  e^L = 2+√3.
print(f"    e^L == 2+√3          : "
      f"{sp.simplify(sp.exp(L2) - (2 + sp.sqrt(3))) == 0}")
print(f"    |sympy - quad| < 1e-8: {abs(float(L2) - L2_num) < 1e-8}")

# --- Cumulative arc length L(t) next to the curve ---
tgrid = np.linspace(0, 4, 400)
ds1_num = sp.lambdify(x, ds1, 'numpy')
Lcum = cumulative_trapezoid(ds1_num(tgrid), tgrid, initial=0.0)
print(f"\n    Cumulative length: L(0) = {Lcum[0]:.6f}, L(4) = {Lcum[-1]:.9f}")
print(f"    L(4) ≈ L (sympy)     : {abs(Lcum[-1] - float(L1)) < 1e-4}")

fig, axs = plt.subplots(1, 2, figsize=(10, 4))
axs[0].plot(tgrid, tgrid**1.5, 'b-', lw=2)
axs[0].set_title(r'The curve $y=x^{3/2}$ on $[0,4]$')
axs[0].set_xlabel('x'); axs[0].set_ylabel('y'); axs[0].grid(True, alpha=0.3)
axs[1].plot(tgrid, Lcum, 'g-', lw=2,
            label=r"$L(t)=\int_0^t\sqrt{1+[f'(u)]^2}\,du$")
axs[1].axhline(float(L1), color='r', ls='--', lw=1,
               label=f'total length = {float(L1):.6f}')
axs[1].set_title('C. Cumulative arc length')
axs[1].set_xlabel('t'); axs[1].set_ylabel('L(t)')
axs[1].legend(); axs[1].grid(True, alpha=0.3)
plt.tight_layout()


# ============================================================
# D. PHYSICAL APPLICATIONS
# ============================================================
print("\n=== D. PHYSICAL APPLICATIONS ===")

# D1. Work of a spring: F(x) = 200x N, x from 0 to 0.1 m
F_elat = 200*x
W = sp.integrate(F_elat, (x, 0, sp.Rational(1, 10)))
print(f"\nD1. Work of a spring, F(x) = 200x N, x ∈ [0, 0.1] m")
print(f"    W = ∫_0^0.1 200x dx = {W} J = {float(W)} J   (expected 1 J)")
print(f"    formula k·x²/2 = {200*sp.Rational(1,10)**2/2} J, matches: "
      f"{sp.simplify(W - 200*sp.Rational(1,10)**2/2) == 0}")

# D2. Centroid of the region under y = x^2, [0,3]
fy = x**2
Ar = sp.integrate(fy, (x, 0, 3))
xbar = sp.integrate(x*fy, (x, 0, 3)) / Ar
ybar = sp.integrate(fy**2/2, (x, 0, 3)) / Ar
print(f"\nD2. Centroid of the region under y = x², [0,3]")
print(f"    A = {Ar}   (expected 9)")
print(f"    x̄ = {xbar} = {float(xbar)}   (expected 9/4 = 2.25)")
print(f"    ȳ = {ybar} = {float(ybar)}   (expected 27/10 = 2.7)")
print(f"    checks: {Ar == 9}, {xbar == sp.Rational(9,4)}, {ybar == sp.Rational(27,10)}")

# D3. Hydrostatic force on the vertical wall of a rectangular tank
#     width w = 4 m, depth d = 3 m, rho·g = 9810 N/m^3
#     F = rho·g * ∫_0^d h * w dh   (h = depth below the surface)
h = sp.symbols('h', nonnegative=True)
rho_g, w_pl, d_bath = 9810, 4, 3
F_ydro = rho_g * sp.integrate(h * w_pl, (h, 0, d_bath))
print(f"\nD3. Hydrostatic force on a vertical wall {w_pl} m × {d_bath} m")
print(f"    rho·g = {rho_g} N/m³")
print(f"    F = rho·g·∫_0^{d_bath} h·{w_pl} dh = {F_ydro} N = {float(F_ydro)/1000:.3f} kN")
print(f"    (expected 9810·4·3²/2 = 176580 N)")
F_typos = sp.Rational(rho_g * w_pl * d_bath**2, 2)
print(f"    formula F = rho·g·w·d²/2 = {F_typos} N, matches: "
      f"{sp.simplify(F_ydro - F_typos) == 0}")
# The center of pressure lies at the depth (∫h·h·w dh)/(∫h·w dh)
h_cp = sp.integrate(h*h*w_pl, (h, 0, d_bath)) / sp.integrate(h*w_pl, (h, 0, d_bath))
print(f"    center of pressure at depth {h_cp} m = {float(h_cp)} m   (= 2d/3 = 2.0 m)")

# --- Pressure distribution plot ---
hh = np.linspace(0, d_bath, 200)
plt.figure(figsize=(6.5, 4.2))
plt.fill_betweenx(hh, 0, rho_g*hh/1000, alpha=0.35, color='tab:cyan',
                  label=f'F = {float(F_ydro)/1000:.2f} kN (width {w_pl} m)')
plt.plot(rho_g*hh/1000, hh, 'b-', lw=2, label='p(h) = rho·g·h')
plt.axhline(float(h_cp), color='r', ls='--', lw=1,
            label=f'center of pressure h = {float(h_cp)} m')
plt.gca().invert_yaxis()
plt.xlabel('pressure p (kPa)'); plt.ylabel('depth h (m)')
plt.title('D. Hydrostatic pressure on a tank wall 4 m × 3 m')
plt.legend(); plt.grid(True, alpha=0.3)
plt.tight_layout()

print("\nDone.")
plt.show()
