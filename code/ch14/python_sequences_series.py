# ============================================================
# python_sequences_series.py
# Chapter 13 — Sequences and Series
# Matzakos, N. (2026). Elements of Linear Algebra, Differential & Integral Calculus. NewTech Publications.
# ============================================================
#
# LIBRARIES:
#   sympy              → limits, symbolic sum, Taylor
#   numpy              → numerical sequences & series
#   matplotlib         → convergence plots, partial sums
#
# BASIC COMMANDS:
#   sympy.limit(a_n, n, oo)           → limit of a sequence
#   sympy.summation(a_n, (n, 1, oo))  → sum of a series
#   sympy.series(f, x, 0, n)          → Taylor/Maclaurin series
# ============================================================

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec
from sympy import (symbols, limit, oo, summation, Sum, factorial,
                   series, sin, cos, exp, log, Rational, pi,
                   sqrt, simplify, lambdify, pprint, S, zoo)
from math import factorial as mfact

n, k, x = symbols('n k x', positive=True)

print("=" * 55)
print(" Chapter 13: Sequences and Series — Python")
print("=" * 55)

# ── A. Sequences — Convergence / Divergence ──────────
print("\n── A. Sequences ──")

sequences = [
    (n/(n+1),           "n/(n+1)",      True),
    ((2*n**2-1)/n**2,   "(2n²-1)/n²",  True),
    ((-1)**n/n,         "(-1)^n/n",    True),
    ((1 + 1/n)**n,      "(1+1/n)^n",  True),
    (n**2/exp(n),       "n²/e^n",      True),
    (n,                 "n",           False),
]

print(f"{'sequence':<18} {'lim':>12}  {'convergence'}")
print("-" * 44)
for a_n, label, conv in sequences:
    try:
        L = limit(a_n, n, oo)
        converges = (L != oo and L != -oo and L != zoo)
        print(f"  {label:<16}  {str(L):>14}  {'✓ Converges' if converges else '✗ Diverges'}")
    except Exception as e:
        print(f"  {label:<16}  {'?':>14}  (see sympy)")

# First 10 terms numerically
print("\nFirst 10 terms a_n = (1+1/n)^n (→ e):")
terms_e = [(1 + 1/i)**i for i in range(1, 11)]
for i, v in enumerate(terms_e, 1):
    print(f"  a_{i:2d} = {v:.8f}  (error vs e: {abs(v - np.e):.2e})")

# ── B. Geometric Series ─────────────────────────
print("\n── B. Geometric Series ──")

geo_cases = [
    (Rational(1,2),  "1/2"),
    (Rational(2,3),  "2/3"),
    (Rational(-1,3), "-1/3"),
    (Rational(1,4),  "1/4"),
]

print(f"{'r':>6}  {'Sum r^n (n=0..oo)':>18}  {'float':>12}")
for r, rlabel in geo_cases:
    S = summation(r**n, (n, 0, oo))
    print(f"  r={rlabel:<6}  {str(S):>18}  {float(S):>12.8f}")

# Telescoping Sum 1/(n(n+1))
print("\nTelescoping Sum 1/(n(n+1)) = 1:")
S_tel = summation(1/(n*(n+1)), (n, 1, oo))
print(f"  Exact: {S_tel}")
print("  Partial sums S_N:")
partial = [sum(1/(i*(i+1)) for i in range(1, N+1)) for N in [5, 10, 20, 50]]
for N, SN in zip([5, 10, 20, 50], partial):
    print(f"    N={N:3d}: S_N = {SN:.10f}  (error={abs(SN-1):.2e})")

# ── C. Convergence Tests ───────────────────────
print("\n── C. Convergence Tests ──")

# Ratio test (D'Alembert), numerically
def ratio_test(a_func, N=50):
    """Computes |a_{n+1}/a_n| for large n"""
    ratios = [abs(a_func(i+1)/a_func(i)) for i in range(1, N+1)]
    return ratios[-1]

ratio_cases = [
    (lambda i: mfact(i)/i**i,   "Sum n!/n^n",   "< 1 → CONVERGES"),
    (lambda i: i**i/mfact(i),   "Sum n^n/n!",   "> 1 → DIVERGES"),
    (lambda i: i**2/2**i,       "Sum n²/2^n",   "< 1 → CONVERGES"),
    (lambda i: 2**i/mfact(i),   "Sum 2^n/n!",   "< 1 → CONVERGES"),
]

print("Ratio Test (|a_{n+1}/a_n| at n=50):")
for a_func, label, verdict in ratio_cases:
    try:
        L = ratio_test(a_func)
        print(f"  {label:<14}: L ≈ {L:.6f}  {verdict}")
    except OverflowError:
        print(f"  {label:<14}: overflow — {verdict}")

# Basel series: Sum 1/n² = pi²/6
print("\n── C2. Convergence of Sum 1/n² → pi²/6 ──")
exact = np.pi**2/6
for N in [10, 100, 1_000, 10_000]:
    SN = sum(1/i**2 for i in range(1, N+1))
    print(f"  N={N:6d}: S_N = {SN:.10f}  error = {abs(SN-exact):.2e}")

# ── D. Taylor / Maclaurin Series ──────────────────
print("\n── D. Maclaurin Series ──")

maclaurin_cases = [
    (exp(x),    "e^x"),
    (sin(x),    "sin x"),
    (cos(x),    "cos x"),
    (1/(1-x),   "1/(1-x)"),
    (log(1+x),  "ln(1+x)"),
]

for f_sym, label in maclaurin_cases:
    T = series(f_sym, x, 0, 7)
    print(f"  {label}: {T}")

# Numerical convergence of e^x at x=1
print("\nConvergence of Maclaurin e^x at x=1:")
for n_terms in [3, 5, 8, 12, 15]:
    approx = sum(1/mfact(k) for k in range(n_terms+1))
    err = abs(approx - np.e)
    print(f"  n={n_terms:2d}: {approx:.12f}  error={err:.2e}")

# ── E. Plots ───────────────────────────────
print("\n── E. Plots ──")

fig = plt.figure(figsize=(14, 9))
fig.suptitle("Sequences and Series", fontsize=13, fontweight='bold')
gs = gridspec.GridSpec(2, 3, fig, hspace=0.45, wspace=0.35)

# 1. Sequence (1+1/n)^n → e
ax1 = fig.add_subplot(gs[0, 0])
ns1  = np.arange(1, 51)
an1  = (1 + 1/ns1)**ns1
ax1.plot(ns1, an1, 'o-', color='royalblue', ms=4, lw=1.5, label=r'$(1+1/n)^n$')
ax1.axhline(np.e, color='tomato', ls='--', lw=2, label=f'$e={np.e:.4f}$')
ax1.set_xlabel('n'); ax1.set_title(r"$(1+\frac{1}{n})^n \to e$", fontsize=10)
ax1.legend(fontsize=8); ax1.grid(True, alpha=0.3)

# 2. Geometric series: partial sums of Sum (1/2)^n
ax2 = fig.add_subplot(gs[0, 1])
ns2  = np.arange(0, 20)
an2  = 0.5**ns2
SN2  = np.cumsum(an2)
ax2.bar(ns2, an2, alpha=0.5, color='royalblue', label=r'$a_n=(1/2)^n$')
ax2.plot(ns2, SN2, 'o-', color='tomato', ms=5, lw=1.8, label=r'$S_N \to 2$')
ax2.axhline(2, color='tomato', ls='--', lw=1.5)
ax2.set_xlabel('N'); ax2.set_title(r"$\sum(1/2)^n \to 2$", fontsize=10)
ax2.legend(fontsize=8); ax2.grid(True, alpha=0.3)

# 3. Convergence of Sum 1/n² → pi²/6
ax3 = fig.add_subplot(gs[0, 2])
ns3  = np.arange(1, 200)
SN3  = np.cumsum(1/ns3**2)
ax3.plot(ns3, SN3, 'royalblue', lw=2, label=r'$S_N = \sum_{k=1}^N 1/k^2$')
ax3.axhline(np.pi**2/6, color='tomato', ls='--', lw=2,
            label=r'$\pi^2/6$')
ax3.set_xlabel('N'); ax3.set_title(r"$\sum 1/n^2 \to \pi^2/6$", fontsize=10)
ax3.legend(fontsize=8); ax3.grid(True, alpha=0.3)

# 4. Maclaurin for e^x — convergence
ax4 = fig.add_subplot(gs[1, 0])
xv4 = np.linspace(-3, 3, 400)
ax4.plot(xv4, np.exp(xv4), 'k', lw=2.5, label=r'$e^x$')
colors4 = ['royalblue', 'tomato', 'forestgreen', 'orange']
for order, col in zip([1, 3, 5, 9], colors4):
    T4 = sum(xv4**k / mfact(k) for k in range(order+1))
    ax4.plot(xv4, T4, ls='--', lw=1.5, color=col,
             label=f'n={order}')
ax4.set_ylim(-5, 15); ax4.set_xlim(-3, 3)
ax4.set_title(r"Maclaurin $e^x$", fontsize=10)
ax4.legend(fontsize=8); ax4.grid(True, alpha=0.3)

# 5. Maclaurin for sinx
ax5 = fig.add_subplot(gs[1, 1])
xv5 = np.linspace(-2*np.pi, 2*np.pi, 500)
ax5.plot(xv5, np.sin(xv5), 'k', lw=2.5, label=r'$\sin x$')
for order, col in zip([1, 3, 5, 9], colors4):
    T5 = sum((-1)**k * xv5**(2*k+1) / mfact(2*k+1) for k in range((order+1)//2 + 1))
    ax5.plot(xv5, T5, ls='--', lw=1.5, color=col, label=f'n={2*((order+1)//2+1)-1}')
ax5.set_ylim(-3, 3); ax5.set_xlim(-2*np.pi, 2*np.pi)
ax5.set_title(r"Maclaurin $\sin x$", fontsize=10)
ax5.legend(fontsize=8); ax5.grid(True, alpha=0.3)

# 6. Convergence error of Sum 1/n² (log-log)
ax6 = fig.add_subplot(gs[1, 2])
ns6  = np.logspace(0, 4, 100).astype(int)
ns6  = np.unique(ns6)
errs6 = [abs(sum(1/i**2 for i in range(1, N+1)) - np.pi**2/6) for N in ns6]
ax6.loglog(ns6, errs6, 'royalblue', lw=2, label='error')
ax6.loglog(ns6, 1/ns6.astype(float), 'tomato', ls='--', lw=1.5, label='1/N')
ax6.set_xlabel('N'); ax6.set_ylabel('|error|')
ax6.set_title(r"Convergence of $\sum 1/n^2$ (log-log)", fontsize=10)
ax6.legend(fontsize=8); ax6.grid(True, alpha=0.3, which='both')

plt.savefig("sequences_series.png", dpi=120, bbox_inches='tight')
print("Plot saved: sequences_series.png")
plt.show()
