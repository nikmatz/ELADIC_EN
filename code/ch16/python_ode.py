# ============================================================
# python_ode.py
# Chapter 15 — Differential Equations
# Matzakos, N. (2026). Elements of Linear Algebra, Differential & Integral Calculus. NewTech Publications.
# ============================================================
#
# LIBRARIES:
#   sympy              → ode, dsolve, classify_ode
#   scipy.integrate    → solve_ivp (numerical solution)
#   numpy              → numerical solutions
#   matplotlib         → solutions and phase portraits
#
# BASIC COMMANDS:
#   sympy.dsolve(eq, f(x))          → general solution of an ODE
#   sympy.classify_ode(eq)          → classification of an ODE
#   scipy.integrate.solve_ivp       → numerical solution
# ============================================================

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec
from sympy import (symbols, Function, dsolve, classify_ode,
                   Eq, diff, exp, sin, cos, tan, sqrt,
                   simplify, lambdify, pprint, pi, E,
                   solve, Rational, log)
from scipy.integrate import solve_ivp

x, t = symbols('x t')
y    = Function('y')
P    = Function('P')

print("=" * 55)
print(" Chapter 15: Differential Equations — Python")
print("=" * 55)

# ── A. Separable Variables ──────────────────────
print("\n── A. Separable Variables ──")

sep_cases = [
    (Eq(diff(y(x),x), x*y(x)),            "dy/dx = x·y"),
    (Eq(diff(y(x),x), y(x)**2),           "dy/dx = y²"),
    (Eq(diff(y(x),x), (x**2+1)/(y(x)+1)),"dy/dx = (x²+1)/(y+1)"),
]

for eq, label in sep_cases:
    sol = dsolve(eq, y(x))
    ode_type = classify_ode(eq, y(x))[0]
    print(f"  {label}  [{ode_type}]")
    print(f"    {sol}")

# Particular solution: dy/dx = x·y, y(0)=2
eq_sp = Eq(diff(y(x),x), x*y(x))
sol_sp = dsolve(eq_sp, y(x), ics={y(0): 2})
print(f"\n  Particular solution dy/dx=x·y, y(0)=2:")
print(f"    {sol_sp}")

# ── B. Linear 1st Order ODEs ────────────────────
print("\n── B. Linear 1st Order ODEs: y' + P(x)y = Q(x) ──")

linear_cases = [
    (Eq(diff(y(x),x) + 2*y(x), 4*x),          "y' + 2y = 4x"),
    (Eq(diff(y(x),x) - y(x)/x, x**2),          "y' - y/x = x²"),
    (Eq(x*diff(y(x),x) + y(x), x*sin(x)),      "x·y' + y = x·sinx"),
]

for eq, label in linear_cases:
    sol = dsolve(eq, y(x))
    print(f"  {label}")
    print(f"    {sol}")

# With an initial condition
eq_lin = Eq(diff(y(x),x) + 2*y(x), 4*x)
sol_lin = dsolve(eq_lin, y(x), ics={y(0): 1})
print(f"\n  Particular solution y'+2y=4x, y(0)=1:")
print(f"    {sol_lin}")

# ── C. 2nd Order ODEs — Homogeneous ───────────────
print("\n── C. 2nd Order ODEs: ay'' + by' + cy = 0 ──")

hom_cases = [
    (Eq(diff(y(x),x,2) - 5*diff(y(x),x) + 6*y(x), 0),
     "y'' - 5y' + 6y = 0", "r=2,3 (real)"),
    (Eq(diff(y(x),x,2) + 4*diff(y(x),x) + 4*y(x), 0),
     "y'' + 4y' + 4y = 0", "r=-2 (double)"),
    (Eq(diff(y(x),x,2) + 4*y(x), 0),
     "y'' + 4y = 0",        "r=±2i (complex)"),
    (Eq(diff(y(x),x,2) + 2*diff(y(x),x) + 5*y(x), 0),
     "y'' + 2y' + 5y = 0",  "r=-1±2i (damped)"),
]

for eq, label, note in hom_cases:
    sol = dsolve(eq, y(x))
    print(f"  {label}  [{note}]")
    print(f"    {sol}")

# Particular solution y''+4y=0, y(0)=1, y'(0)=0
eq_shm = Eq(diff(y(x),x,2) + 4*y(x), 0)
sol_shm = dsolve(eq_shm, y(x), ics={y(0): 1, diff(y(x),x).subs(x,0): 0})
print(f"\n  Particular y''+4y=0, y(0)=1, y'(0)=0:")
print(f"    {sol_shm}")

# ── D. Non-homogeneous 2nd Order ODEs ───────────────
print("\n── D. Non-homogeneous: ay'' + by' + cy = f(x) ──")

inhom_cases = [
    (Eq(diff(y(x),x,2) - 3*diff(y(x),x) + 2*y(x), exp(x)),
     "y'' - 3y' + 2y = e^x"),
    (Eq(diff(y(x),x,2) + y(x), sin(x)),
     "y'' + y = sinx  (resonance)"),
    (Eq(diff(y(x),x,2) + 2*diff(y(x),x) + 5*y(x), 10*cos(2*x)),
     "y'' + 2y' + 5y = 10cos(2x)"),
]

for eq, label in inhom_cases:
    sol = dsolve(eq, y(x))
    print(f"  {label}")
    print(f"    {sol}")

# ── E. Applications ──────────────────────────
print("\n── E. Applications ──")

# E1. Exponential growth/decay: dP/dt = k·P
print("  Malthus model: dP/dt = k·P")
k_growth = 0.03
P_func   = lambda t_val: 1000 * np.exp(k_growth * t_val)
for yr in [0, 10, 25, 50]:
    print(f"    P({yr}) = {P_func(yr):.0f}")

# E2. Logistic growth: dP/dt = r·P·(1 - P/K)
print("\n  Logistic model: dP/dt = 0.1·P·(1 - P/1000)")
r_log, K_log = 0.1, 1000.0

def logistic(t_val, P_val):
    return r_log * P_val[0] * (1 - P_val[0]/K_log)

sol_log = solve_ivp(logistic, [0, 100], [50], dense_output=True)
t_log   = np.linspace(0, 100, 300)
P_log   = sol_log.sol(t_log)[0]
print(f"    P(0)=50, P(50)≈{P_log[150]:.0f}, P(100)≈{P_log[-1]:.0f}")

# E3. Mechanical oscillation: my'' + cy' + ky = 0
print("\n  Damped Oscillation: y'' + 2y' + 5y = 0")
def damped(t_val, yv):
    return [yv[1], -2*yv[1] - 5*yv[0]]

sol_damp = solve_ivp(damped, [0, 10], [1, 0], dense_output=True)
t_damp   = np.linspace(0, 10, 400)
y_damp   = sol_damp.sol(t_damp)

# E4. RC circuit: RC·dQ/dt + Q = E·C, RC=0.1, E=10V
print("  RC circuit: 0.1·dQ/dt + Q = 1  (Q(0)=0)")
RC_val = 0.1

def rc_circuit(t_val, Q):
    return [(1 - Q[0]) / RC_val]

sol_rc = solve_ivp(rc_circuit, [0, 1], [0], dense_output=True)
t_rc   = np.linspace(0, 1, 300)
Q_rc   = sol_rc.sol(t_rc)[0]
print(f"    Q(0.1s)≈{Q_rc[30]:.4f},  Q(inf)→1.0 (=E·C)")

# ── F. Numerical Solution & Phase Portraits ───────────
print("\n── F. Plots ──")

fig = plt.figure(figsize=(14, 9))
fig.suptitle("Differential Equations", fontsize=13, fontweight='bold')
gs = gridspec.GridSpec(2, 3, fig, hspace=0.45, wspace=0.35)

# 1. Separable — solutions of dy/dx = x·y for various C
ax1 = fig.add_subplot(gs[0, 0])
xv1 = np.linspace(-2, 2, 400)
for C_val, col in zip([-2, -1, 1, 2], ['royalblue','tomato','forestgreen','orange']):
    ax1.plot(xv1, C_val*np.exp(xv1**2/2), lw=1.8, color=col, label=f'C={C_val}')
ax1.set_ylim(-6, 6); ax1.set_xlim(-2, 2)
ax1.axhline(0, color='k', lw=0.5); ax1.axvline(0, color='k', lw=0.5)
ax1.set_title(r"$dy/dx = xy$: family of solutions", fontsize=10)
ax1.legend(fontsize=7); ax1.grid(True, alpha=0.3)

# 2. Linear ODE: y' + 2y = 4x — particular solution
ax2 = fig.add_subplot(gs[0, 1])
xv2 = np.linspace(0, 3, 300)
# General: y = 2x - 1 + C·e^(-2x)
for C_val, col in zip([-2, 0, 1, 3], ['royalblue','tomato','forestgreen','orange']):
    ax2.plot(xv2, 2*xv2 - 1 + C_val*np.exp(-2*xv2), lw=1.8, color=col,
             label=f'C={C_val}')
ax2.plot(xv2, 2*xv2 - 1 + 2*np.exp(-2*xv2), 'k', lw=2.5, ls='--', label='y(0)=1')
ax2.set_title(r"$y'+2y=4x$: family of solutions", fontsize=10)
ax2.legend(fontsize=7); ax2.grid(True, alpha=0.3)

# 3. Damped oscillation
ax3 = fig.add_subplot(gs[0, 2])
ax3.plot(t_damp, y_damp[0], 'royalblue', lw=2.5, label='y(t) — damping')
ax3.plot(t_damp, y_damp[1], 'tomato', lw=1.5, ls='--', label="y'(t)")
envelope = np.exp(-t_damp)
ax3.plot(t_damp,  envelope, 'gray', lw=1, ls=':')
ax3.plot(t_damp, -envelope, 'gray', lw=1, ls=':')
ax3.axhline(0, color='k', lw=0.5)
ax3.set_title(r"$y''+2y'+5y=0$: damped oscillation", fontsize=10)
ax3.legend(fontsize=8); ax3.grid(True, alpha=0.3)

# 4. Logistic model vs exponential
ax4 = fig.add_subplot(gs[1, 0])
t4  = np.linspace(0, 100, 300)
P_exp = 50 * np.exp(r_log * t4)
ax4.plot(t4, P_log, 'royalblue', lw=2.5, label='Logistic')
ax4.plot(t4, np.clip(P_exp, 0, 1200), 'tomato', lw=1.8, ls='--', label='Exponential')
ax4.axhline(K_log, color='gray', ls=':', lw=1.5, label=f'K={K_log:.0f}')
ax4.set_xlabel('t (years)'); ax4.set_ylabel('P(t)')
ax4.set_title("Logistic vs Exponential model", fontsize=10)
ax4.legend(fontsize=8); ax4.grid(True, alpha=0.3)

# 5. RC circuit
ax5 = fig.add_subplot(gs[1, 1])
ax5.plot(t_rc, Q_rc, 'royalblue', lw=2.5, label='Q(t)')
ax5.plot(t_rc, 1 - Q_rc, 'tomato', lw=1.8, ls='--', label='V_C(t)=1-Q(t)')
ax5.axhline(1, color='gray', ls=':', lw=1)
ax5.set_xlabel('t (s)'); ax5.set_ylabel('Q (C)')
ax5.set_title("RC circuit: charging", fontsize=10)
ax5.legend(fontsize=8); ax5.grid(True, alpha=0.3)

# 6. Phase portrait y'' + 2y' + 5y = 0
ax6 = fig.add_subplot(gs[1, 2])
for y0, v0, col in zip([1, 2, -1, 0.5], [0, 0, 0, 2],
                        ['royalblue','tomato','forestgreen','orange']):
    sol_ph = solve_ivp(damped, [0, 12], [y0, v0], dense_output=True)
    t_ph   = np.linspace(0, 12, 500)
    yph    = sol_ph.sol(t_ph)
    ax6.plot(yph[0], yph[1], lw=1.8, color=col,
             label=f'({y0},{v0})')
ax6.axhline(0, color='k', lw=0.5); ax6.axvline(0, color='k', lw=0.5)
ax6.set_xlabel('y'); ax6.set_ylabel("y'")
ax6.set_title("Phase Portrait: damped oscillation", fontsize=10)
ax6.legend(fontsize=7); ax6.grid(True, alpha=0.3)

plt.savefig("ode_solutions.png", dpi=120, bbox_inches='tight')
print("Plot saved: ode_solutions.png")
plt.show()
