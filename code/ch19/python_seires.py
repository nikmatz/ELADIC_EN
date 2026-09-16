# python_seires.py — Sequences, Series and Convergence Tests (Ch. 19)
# Matzakos, N. (2026). Elements of Linear Algebra, Differential & Integral Calculus. NewTech Publications.
# Commands: sympy.limit(), sympy.summation(), np.cumsum(), math.factorial(), matplotlib.pyplot

import math
import numpy as np
import sympy as sp
import matplotlib.pyplot as plt

n = sp.symbols('n', positive=True)
k = sp.symbols('k', integer=True, positive=True)

print("=" * 60)
print("SEQUENCES, SERIES AND CONVERGENCE TESTS")
print("=" * 60)

# ── A. Limits of sequences ──────────────────────────────────────────────────
print()
print("A. LIMITS OF SEQUENCES  (sympy.limit)")
print("-" * 60)
seqs = [
    (n / (n + 1),        "n/(n+1)",     "1"),
    ((1 + 1/n)**n,       "(1+1/n)^n",   "e"),
    (n**2 / sp.exp(n),   "n²/eⁿ",       "0"),
]
for expr, label, expected in seqs:
    L = sp.limit(expr, n, sp.oo)
    print(f"   lim {label:12s} = {str(L):8s}   (expected {expected})")

# sympy.limit does not handle the factor (-1)ⁿ; we use the squeeze theorem:
# |(-1)ⁿ/n| = 1/n -> 0, hence (-1)ⁿ/n -> 0 as well.
Labs = sp.limit(sp.Abs(1/n), n, sp.oo)
print(f"   lim {'(-1)ⁿ/n':12s} : squeeze theorem, lim |(-1)ⁿ/n| = lim 1/n = "
      f"{Labs}  =>  limit 0   (expected 0)")

alt = (-1)**n / n
print()
print("   First 10 terms:")
for expr, label in [(e_, l_) for e_, l_, _ in seqs] + [(alt, "(-1)ⁿ/n")]:
    terms = [float(expr.subs(n, m)) for m in range(1, 11)]
    print(f"      {label:12s}: " + ", ".join(f"{t:+.5f}" for t in terms))

# Plot: (1+1/n)^n -> e (horizontal asymptote)
nv = np.arange(1, 201)
seq_e = (1 + 1.0 / nv) ** nv
plt.figure(figsize=(7, 4.2))
plt.plot(nv, seq_e, 'b.-', ms=3, lw=0.8, label=r'$(1+1/n)^n$')
plt.axhline(np.e, color='r', ls='--', label=f'e = {np.e:.6f} (horizontal asymptote)')
plt.xlabel('n'); plt.ylabel(r'$a_n$')
plt.ylim(1.9, 2.9)
plt.title(r'The sequence $(1+1/n)^n$ converges to $e$')
plt.legend(); plt.grid(True, alpha=0.3)
plt.tight_layout()
print(f"   a_200 = {seq_e[-1]:.8f}   e = {np.e:.8f}   difference = {np.e - seq_e[-1]:.3e}")

# ── B. Geometric series ─────────────────────────────────────────────────────
print()
print("B. GEOMETRIC SERIES  Sum_{n=0}^∞ rⁿ = 1/(1-r)")
print("-" * 60)
plt.figure(figsize=(7, 4.2))
Nmax = 30
idx = np.arange(Nmax + 1)
for r, col in [(0.5, 'tab:blue'), (2/3, 'tab:orange'), (-0.5, 'tab:green')]:
    rr = sp.Rational(1, 2) if r == 0.5 else (sp.Rational(2, 3) if r > 0 else sp.Rational(-1, 2))
    exact = sp.summation(rr**k, (k, 0, sp.oo))
    S = np.cumsum(r ** idx)                      # partial sums with np.cumsum
    print(f"   r = {str(rr):5s}: sympy = {str(exact):5s} = {float(exact):.8f}   "
          f"1/(1-r) = {1/(1-r):.8f}   S_30 = {S[-1]:.8f}")
    plt.plot(idx, S, 'o-', ms=3, color=col, label=f'r = {rr}')
    plt.axhline(float(exact), color=col, ls='--', lw=1)
print("   (expected: 2, 3, 2/3)")
plt.xlabel('N'); plt.ylabel(r'$S_N=\sum_{n=0}^{N} r^n$')
plt.title('Partial sums of geometric series (dashed: the limits)')
plt.legend(); plt.grid(True, alpha=0.3)
plt.tight_layout()

# ── C. Ratio test (numerically, N=50) and the Basel series ──────────────────
print()
print("C. NUMERICAL RATIO TEST  (N = 50 terms)")
print("-" * 60)
N = 50
ns = np.arange(1, N + 1)
a1 = np.array([math.factorial(int(m)) / float(m) ** int(m) for m in ns])   # n!/nⁿ
a2 = np.array([float(m) ** int(m) / math.factorial(int(m)) for m in ns])   # nⁿ/n!
r1 = a1[1:] / a1[:-1]
r2 = a2[1:] / a2[:-1]
print(f"   Sum n!/nⁿ : ratio a_50/a_49 = {r1[-1]:.10f}   -> 1/e = {1/np.e:.10f}"
      f"   ({'< 1  CONVERGES' if r1[-1] < 1 else '>= 1'})")
print(f"               S_50 = {a1.sum():.10f}")
print(f"   Sum nⁿ/n! : ratio a_50/a_49 = {r2[-1]:.10f}   -> e   = {np.e:.10f}"
      f"   ({'> 1  DIVERGES' if r2[-1] > 1 else '<= 1'})")
print(f"               S_50 = {a2.sum():.6e}  (it explodes)")

print()
print("   Sum 1/n² -> pi²/6 : error in log-log")
Nb = 2000
nb = np.arange(1, Nb + 1)
Sb = np.cumsum(1.0 / nb**2)
err = np.pi**2 / 6 - Sb
for N0 in (10, 100, 1000):
    print(f"      S_{N0:<5d} = {Sb[N0-1]:.10f}   error = {err[N0-1]:.3e}"
          f"   (1/N = {1.0/N0:.3e})")
slope = np.polyfit(np.log(nb[9:]), np.log(err[9:]), 1)[0]
print(f"      Slope of log(error) versus log(N) = {slope:.4f}   (expected -1)")

plt.figure(figsize=(7, 4.2))
plt.loglog(nb, err, 'b-', label=r'$\pi^2/6-S_N$')
plt.loglog(nb, 1.0 / nb, 'r--', label=r'$1/N$ (slope $-1$)')
plt.xlabel('N'); plt.ylabel('error')
plt.title(r'Error of $\sum 1/n^2$ — a line of slope $-1$ in log-log')
plt.legend(); plt.grid(True, which='both', alpha=0.3)
plt.tight_layout()

# ── D. A telescoping series versus a divergent one ──────────────────────────
print()
print("D. TELESCOPING SERIES")
print("-" * 60)
Nt = 1000
nt = np.arange(1, Nt + 1)
tele = np.cumsum(1.0 / np.sqrt(nt) - 1.0 / np.sqrt(nt + 1))   # -> 1
logs = np.cumsum(np.log(1.0 + 1.0 / nt))                      # = ln(N+1), diverges
print("   Sum (1/√n - 1/√(n+1))  = 1 - 1/√(N+1)  ->  1")
for N0 in (10, 100, 1000):
    print(f"      S_{N0:<5d} = {tele[N0-1]:.10f}   closed form 1-1/√(N+1) = "
          f"{1 - 1/np.sqrt(N0+1):.10f}")
print("   Sum ln(1+1/n) = ln(N+1)  ->  +∞  (diverges)")
for N0 in (10, 100, 1000):
    print(f"      S_{N0:<5d} = {logs[N0-1]:.10f}   ln({N0+1}) = {np.log(N0+1):.10f}")
print(f"   Maximum deviation from the closed forms: "
      f"{max(np.max(np.abs(tele - (1 - 1/np.sqrt(nt+1)))), np.max(np.abs(logs - np.log(nt+1)))):.2e}")
print("   CONCLUSION: in both of them the terms tend to 0, but only the first")
print("   has bounded partial sums. a_n -> 0 is NOT enough for convergence.")

plt.figure(figsize=(7.5, 4.5))
plt.plot(nt, tele, 'b-', lw=2, label=r'$\sum(1/\sqrt{n}-1/\sqrt{n+1})\to 1$')
plt.axhline(1, color='b', ls=':', lw=1)
plt.plot(nt, logs, 'r-', lw=2, label=r'$\sum\ln(1+1/n)=\ln(N+1)\to\infty$')
plt.xscale('log')
plt.xlabel('N (logarithmic axis)'); plt.ylabel(r'$S_N$')
plt.title('A convergent telescoping series versus a divergent one')
plt.legend(); plt.grid(True, alpha=0.3)
plt.tight_layout()
plt.show()
