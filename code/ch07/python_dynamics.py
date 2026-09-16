# ============================================================
# python_dynamics.py
# Κεφάλαιο 7 — Δυναμικά Συστήματα: Τροχιές και Φασικά Πορτρέτα
# Ματζάκος, Ν. (2026). Στοιχεία Γραμμικής Άλγεβρας, Διαφορικού & Ολοκληρωτικού Λογισμού. NewTech Publications.
# ============================================================
#
# ΒΙΒΛΙΟΘΗΚΕΣ:
#   numpy      -> πίνακες, ιδιοτιμές, επαναλήψεις
#   matplotlib -> τροχιές και φασικά πορτρέτα
#
# ΒΑΣΙΚΕΣ ΕΝΤΟΛΕΣ:
#   np.linalg.eigvals(A)  -> ιδιοτιμές
#   A @ x                 -> πολλαπλασιασμός πίνακα επί διάνυσμα
#   np.linalg.eig(P)      -> ιδιοτιμές ΚΑΙ ιδιοδιανύσματα
#   matplotlib.pyplot     -> γραφήματα
# ============================================================

import numpy as np
import matplotlib.pyplot as plt

print("=" * 60)
print(" Κεφάλαιο 7: Δυναμικά Συστήματα — Τροχιές & Φασικά Πορτρέτα")
print("=" * 60)


def spectral_radius(M):
    """Φασματική ακτίνα ρ(M) = max |λ_i|."""
    return float(np.max(np.abs(np.linalg.eigvals(M))))


def stability_verdict(rho, tol=1e-12):
    """Το συμπέρασμα ΠΡΟΚΥΠΤΕΙ από τον έλεγχο — δεν είναι σταθερό κείμενο."""
    if rho < 1 - tol:
        return ("ρ < 1  ->  ασυμπτωτικά ΕΥΣΤΑΘΕΣ: x_k -> 0")
    elif abs(rho - 1) <= tol:
        return ("ρ = 1  ->  ΟΡΙΑΚΗ περίπτωση: η τροχιά παραμένει φραγμένη "
                "και συγκλίνει σε ΜΗ ΜΗΔΕΝΙΚΗ στάσιμη κατάσταση, όχι στο 0")
    else:
        return ("ρ > 1  ->  ΑΣΤΑΘΕΣ: η τροχιά απομακρύνεται (|x_k| -> ∞)")


def trajectory(M, x0, steps):
    """Τροχιά x_{n+1} = M x_n, επιστρέφει πίνακα σχήματος (steps+1, 2)."""
    out = [np.asarray(x0, dtype=float)]
    for _ in range(steps):
        out.append(M @ out[-1])
    return np.array(out)


# ── Α. (α) Τροχιά 50 βημάτων, ιδιοτιμές και ευστάθεια ────────
print("\n[Α] Τροχιά x_{n+1} = A x_n και ευστάθεια μέσω ρ(A)")

A  = np.array([[0.9, 0.1],
               [0.1, 0.9]])
x0 = np.array([1.0, 0.0])

evals = np.linalg.eigvals(A)
rhoA  = spectral_radius(A)
print("  A =", A.tolist())
print("  x0 =", x0.tolist())
print("  Ιδιοτιμές:", np.round(np.real_if_close(evals), 10).tolist(),
      " (= [1,0 ; 0,8] ✓)")
print("  ρ(A) =", round(rhoA, 12), " (= 1,0 ✓)")
print("  ", stability_verdict(rhoA))

traj = trajectory(A, x0, 50)
for k in range(1, 6):
    print(f"  x_{k} = {np.round(traj[k], 6).tolist()}")
print("  x_50 =", np.round(traj[50], 6).tolist(),
      " (-> [0,5 ; 0,5] ✓ — ΟΧΙ στο μηδέν)")

# Το άθροισμα x1+x2 διατηρείται, επειδή το (1,1) είναι αριστερό
# ιδιοδιάνυσμα του A για λ = 1:  1^T A = 1^T.
print("  Διατηρούμενο άθροισμα x1+x2:",
      np.round(traj[:, 0] + traj[:, 1], 10)[[0, 1, 25, 50]].tolist(),
      " (σταθερό = 1 ✓)")
print("  Οριακή κατάσταση θεωρητικά = ((x1+x2)/2, (x1+x2)/2) = [0.5, 0.5] ✓")

# ── Β. (β) Στάσιμη κατανομή αλυσίδας Markov, έλεγχος Pπ = π ──
print("\n[Β] Αλυσίδα Markov: στάσιμη κατανομή π")

P = np.array([[0.9, 0.2],
              [0.1, 0.8]])
print("  P =", P.tolist(), " (στήλες με άθροισμα 1)")

vals, vecs = np.linalg.eig(P)
print("  Ιδιοτιμές του P:", np.round(np.real_if_close(vals), 10).tolist(),
      " (= [1,0 ; 0,7] ✓)")

# Εντοπίζουμε ΠΟΙΑ ιδιοτιμή ισούται με 1 — δεν υποθέτουμε θέση.
i = int(np.argmin(np.abs(vals - 1.0)))
print("  Η λ = 1 βρίσκεται στη θέση:", i, " (λ =", round(float(np.real(vals[i])), 10), ")")

pi = np.real(vecs[:, i])
pi = pi / pi.sum()                      # κανονικοποίηση: άθροισμα 1
print("  π =", np.round(pi, 6).tolist(), " (= [2/3 ; 1/3] = [0,666667 ; 0,333333] ✓)")
print("  Έλεγχος P π = π :", bool(np.allclose(P @ pi, pi)), " (True ✓)")
print("  Έλεγχος Σπ_i = 1 :", bool(np.isclose(pi.sum(), 1.0)), " (True ✓)")
print("  Σφάλμα ||Pπ - π||:", float(np.linalg.norm(P @ pi - pi)))

# ── Γ. (γ) Τροχιά στον χώρο κατάστασης και συνιστώσες ────────
print("\n[Γ] Γραφήματα: χώρος κατάστασης (x1,x2) και συνιστώσες x1(k), x2(k)")

fig1, ax = plt.subplots(1, 2, figsize=(10, 4))

ax[0].plot(traj[:, 0], traj[:, 1], 'o-', ms=3, lw=1, color='tab:blue',
           label='τροχιά')
ax[0].plot(traj[0, 0], traj[0, 1], 's', color='tab:green', ms=9, label='$x_0=(1,0)$')
ax[0].plot(traj[-1, 0], traj[-1, 1], '*', color='tab:red', ms=14,
           label='οριακό $(0{,}5\\,;\\,0{,}5)$')
ax[0].set_xlabel('$x_1$'); ax[0].set_ylabel('$x_2$')
ax[0].set_title('Τροχιά στον χώρο κατάστασης  (ρ(A)=1)')
ax[0].grid(alpha=.3); ax[0].legend(fontsize=8)

ax[1].plot(traj[:, 0], label='$x_1(k)$')
ax[1].plot(traj[:, 1], label='$x_2(k)$')
ax[1].axhline(0.5, color='k', ls='--', lw=.8, label='όριο 0,5')
ax[1].set_xlabel('$k$'); ax[1].set_ylabel('τιμή συνιστώσας')
ax[1].set_title('Συνιστώσες ανά βήμα')
ax[1].grid(alpha=.3); ax[1].legend(fontsize=8)
fig1.tight_layout()

# ── Δ. (δ) ΠΡΟΑΙΡΕΤΙΚΟ: ασταθές σύστημα & σύγκριση πορτρέτων ─
print("\n[Δ] Προαιρετικό: ασταθές σύστημα και σύγκριση φασικών πορτρέτων")

B = np.array([[1.1, 0.2],
              [0.1, 0.9]])
rhoB = spectral_radius(B)
print("  B =", B.tolist())
print("  Ιδιοτιμές του B:", np.round(np.linalg.eigvals(B), 6).tolist(),
      " (= [1,173205 ; 0,826795] ✓)")
print("  ρ(B) =", round(rhoB, 12), " (= 1,173205080757 ✓)")
print("  ", stability_verdict(rhoB))

trB = trajectory(B, x0, 20)
for k in (5, 10, 20):
    print(f"  B^{k} x0 = {np.round(trB[k], 6).tolist()}")
print("  ||x_20|| για A:", round(float(np.linalg.norm(traj[20])), 6),
      " | για B:", round(float(np.linalg.norm(trB[20])), 6),
      " (η δεύτερη πολύ μεγαλύτερη ✓)")

# Ένα τρίτο, γνήσια ευσταθές σύστημα για πλήρη σύγκριση.
C = np.array([[0.8, 0.0],
              [0.0, 0.6]])
print("  C =", C.tolist(), " ρ(C) =", round(spectral_radius(C), 12), " (= 0,8 ✓)")
print("  ", stability_verdict(spectral_radius(C)))

# Φασικά πορτρέτα: πολλές αρχικές συνθήκες πάνω στον μοναδιαίο κύκλο.
theta  = np.linspace(0, 2 * np.pi, 12, endpoint=False)
starts = np.stack([np.cos(theta), np.sin(theta)], axis=1)

fig2, axs = plt.subplots(1, 3, figsize=(13, 4.2))
for axi, (M, name, steps) in zip(
        axs,
        [(C, 'C: ρ=0,8 < 1 — ευσταθές', 25),
         (A, 'A: ρ=1 — οριακό', 40),
         (B, 'B: ρ=1,173 > 1 — ασταθές', 12)]):
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
fig2.suptitle('Φασικά πορτρέτα: πράσινο = αρχή, κόκκινο = τέλος τροχιάς',
              fontsize=10)
fig2.tight_layout()

print("\n  Σύγκριση: στο C οι τροχιές καταρρέουν στο 0· στο A συρρέουν")
print("  στην ευθεία x1 = x2 (ιδιοχώρος της λ=1)· στο B εκτοξεύονται")
print("  κατά τη διεύθυνση του ιδιοδιανύσματος της λ = 1,1732.")

plt.show()
print("\n✓ Ολοκληρώθηκε.")
