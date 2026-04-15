# TODO

## High priority

- [ ] **Contribute `norm_exp_le` to Mathlib** — We proved `‖exp a‖ ≤ exp ‖a‖` for general Banach algebras; Mathlib only has `Complex.norm_exp_le_exp_norm` for `ℂ`. The helpers `norm_exp_sub_one_le`, `exp_sub_one_sub_bound_real`, and `norm_exp_sub_one_sub_le` are also natural additions.

  **PR readiness assessment** (cleanup needed before submitting):
  1. Weaken `[NormOneClass 𝔸]` → use `norm_pow_le'` (works with just `[NormedRing 𝔸]`)
  2. Remove `include 𝕂 in` pattern (non-standard for Mathlib); use section variables instead
  3. Follow Mathlib naming: `norm_exp_le` → `norm_exp_le_exp_norm`, etc.
  4. Drop redundant helpers (`real_exp_summable`, `real_exp_eq_tsum` already in Mathlib)
  5. Target file: `Mathlib.Analysis.Normed.Algebra.Exponential` (modify existing, not new file)
  6. Open a Zulip thread first to confirm maintainer interest before investing effort

- [x] **Tighten the error constant** — Tightened from `C = 2‖A‖‖B‖ exp(2(‖A‖+‖B‖)) + 1` to `C = 2‖A‖‖B‖ exp(‖A‖+‖B‖) + 1`. The `+1` remains for `C > 0`; only `1/n` slack.

## Medium priority

- [x] **Strang splitting convergence (F2a)** — Proved `(exp(A/2n) exp(B/n) exp(A/2n))^n → exp(A+B)` at O(1/n) rate using C1 applied twice. File: `LieTrotter/StrangSplitting.lean`.
- [x] **Strang splitting O(1/n²) rate (F2b)** — Proved O(1/n²) convergence by showing cubic step error O(1/n³). Key: the commutator [a,b] cancels by symmetry in exp(a)exp(b)exp(a), leaving cubic remainder. New lemma `norm_exp_mul_exp_sub_exp_add_sub_comm_le` extracts the commutator from the Lie-Trotter error.

- [x] **Multi-operator Lie-Trotter (G1)** — Generalize from $A+B$ to $A_1 + \cdots + A_m$:
  $$e^{A_1+\cdots+A_m} = \lim_{n\to\infty} (e^{A_1/n} \cdots e^{A_m/n})^n$$
  This is the version used in quantum simulation (Hamiltonians decompose into many terms).
  The proof generalizes by induction on $m$, peeling off one factor at a time:
  ```
  ‖e^{a₁}⋯e^{aₘ₊₁} - e^{a₁+⋯+aₘ₊₁}‖
    ≤ ‖e^{a₁}‖ · ‖e^{a₂}⋯e^{aₘ} - e^{a₂+⋯+aₘ}‖ + ‖e^{a₁}e^{a₂+⋯+aₘ} - e^{a₁+⋯+aₘ}‖
  ```
  Telescopes into a sum of pairwise C1-type bounds. Estimate: ~150 lines. Reuses all existing infrastructure.

- [ ] **Fourth-order Suzuki formula (H1)** — BCH-based approach via cubic coefficient extraction:

  **Core difficulty:** The triangle inequality cannot capture the cubic cancellation. The Suzuki parameter has $1-4p < 0$ (since $p \approx 0.414$), so $|1-4p|^3 \neq (1-4p)^3$ and the norm bound $4|p|^3 + |1-4p|^3 = 8p^3 \neq 0$. We must extract the cubic coefficient $E_3$ as an explicit algebra element and show the signed cancellation $4p^3 + (1-4p)^3 = 0$ kills it.

  **Approach:** Import [Lean-BCH](https://github.com/Jue-Xu/Lean-BCH) as Lake dependency and extend it with:
  - A quartic log series remainder (**done**: `norm_logOnePlus_sub_sub_sub_le`)
  - A fourth-order BCH expansion extracting the degree-3 term `bch_cubic_term` (**scaffolded**, 3 sorry's)
  - Quintic symmetric BCH bound: $\|Z(c\cdot a, c\cdot b) - c(a+b) - c^3 E_3\| \le K c^5 s^5$

  **Implementation plan (see plan file `bright-purring-torvalds.md`):**

  Phase 1 — Extend Lean-BCH (~460 lines):
  1. ✅ Quartic log remainder: $\|\log(1+x) - x + x^2/2 - x^3/3\| \le \|x\|^4/(1-\|x\|)$
  2. Fourth-order BCH expansion: $\text{bch}(a,b) = a+b+\frac{1}{2}[a,b]+E_3(a,b)+O(s^4)$
  3. Quintic symmetric BCH: $E_3(ca,cb) = c^3 E_3(a,b) + O(c^5 s^5)$
  4. $E_3$ norm bound and homogeneity

  Phase 2 — Infrastructure (~50 lines):
  5. Sync Mathlib versions between Lean-BCH and Lean-Trotter
  6. Add `require lean-bch from git` to lakefile

  Phase 3 — Suzuki assembly (~400 lines, new file `LieTrotter/Suzuki4Order4.lean`):
  7. Connect Strang step to BCH log: $S_2(c/n) = \exp(Z_c)$
  8. $S_4$ as palindromic triple product: $\exp(2Z_p) \cdot \exp(Z_q) \cdot \exp(2Z_p)$
  9. Quintic step error: $(4p^3+(1-4p)^3) E_3 = 0$ kills cubic → $O(1/n^5)$
  10. Assembly: $O(1/n^5)$ step → $O(1/n^4)$ total via telescoping
  11. Suzuki parameter existence: $\exists p,\; 4p^3+(1-4p)^3=0$
  12. Main theorem: `suzuki4_convergence_order4`

  **Estimated total: ~900 lines.** Critical path: 1→2→3→5→6→7→8→9→10→12.

- [x] **Truncated BCH bounds ([Lean-BCH](https://github.com/Jue-Xu/Lean-BCH))** — ✅ Complete (0 sorry's before Suzuki extension).
  Proved: `exp_bch`, `norm_bch_sub_add_sub_bracket_le` (H1), `norm_symmetric_bch_sub_add_le` (H2), Lie bracket bridge (M1).

- [ ] **General Suzuki hierarchy (H2)** — Prove convergence of the $2k$-th order Suzuki formula $S_{2k}$ defined recursively:
  $$S_{2k}(t) = S_{2k-2}(p_k t)^2\, S_{2k-2}((1-4p_k)t)\, S_{2k-2}(p_k t)^2, \quad p_k = \frac{1}{4-4^{1/(2k-1)}}$$
  This gives O(1/n^{2k}) convergence. Very ambitious — requires induction on the Suzuki order $k$ and tracking error cancellation at each level. Likely a separate project.

- [x] **Commutator-scaling Trotter error (H)** — Proved `norm_lie_trotter_comm_scaling`: the Trotter error `‖exp(tB)exp(tA) - exp(t(A+B))‖` is bounded by `‖[B,A]‖ · t² · exp(t(‖A‖+3‖B‖))`, replacing the product `‖A‖‖B‖` with the commutator `‖[B,A]‖`. Uses Duhamel formula via FTC-2. File: `LieTrotter/CommutatorScaling.lean` (370 lines, 0 sorry's).

- [x] **Tighten commutator-scaling constant to t²/2** — ✅ Done. Used `norm_integral_le_of_norm_le` (non-constant) + FTC-2 on `x²/2` to evaluate `∫₀ᵗ τ dτ = t²/2`.

- [x] **Multi-operator commutator-scaling** — ✅ Done. File: `LieTrotter/MultiCommutatorScaling.lean` (128 lines). Defines `listCommNorm` (sum of commutator norms with suffix sums) and proves `norm_list_prod_exp_sub_exp_sum_comm`. Matches the Proposition in Childs et al. §VII.A for first-order.

- [ ] **Second-order (Strang) commutator-scaling** — Scaffolded in `LieTrotter/StrangCommutatorScaling.lean` (4 sorry's). Target: recover the Proposition "Tight error bound for the second-order Suzuki formula" from Childs et al. (`prefactor.tex:105`):
  $$\|S_2(t) - e^{tH}\| \le \frac{t^3}{12}\|[B,[B,A]]\| + \frac{t^3}{24}\|[A,[A,B]]\|$$
  **Approach:** Double FTC — apply `exp_conj_sub_eq_integral` twice to extract double commutators `[B,[B,A]]` and `[A,[A,B]]` from the Strang residual. The first-order commutator `[B,A]` cancels by the symmetry of the Strang product (order condition).
  **Key sorry's:**
  1. `exp_conj_sub_comm_eq_double_integral` — double integral of `[B,[B,A]]`
  2. `strang_integral_error` — Duhamel for Strang (4-factor product rule)
  3. `norm_exp_conj_sub_comm_le` — norm bound on double integral remainder
  4. `norm_strang_comm_scaling` — assembly with `t³/12 + t³/24`

- [ ] **Matrix specialization (F1)** — Prove `matrix_lie_trotter` for `Matrix (Fin d) (Fin d) ℂ`. Should be a one-liner applying `lie_trotter` once the `NormOneClass` instance is verified for the matrix norm. Connects to quantum computing applications.

## Low priority

## Publication / dissemination

- [ ] **Zulip announcement + arXiv note** (do first, low effort) — Post to `#general` on [leanprover.zulipchat.com](https://leanprover.zulipchat.com/) announcing the formalization. Write a 1–2 page arXiv companion note (cs.LO or quant-ph) with the repo link. Gets immediate community visibility.

- [ ] **ITP/CPP formalization pearl** (medium effort, peer-reviewed) — 2–4 page short paper covering: (1) the algebraic factorization trick for C1 vs. the standard BCH approach, (2) the commutator cancellation for the cubic Strang bound, (3) the Mathlib API gap (`norm_exp_le` for general Banach algebras). Check submission deadlines.

- [ ] **Companion citation for physics papers** — If writing a paper on Hamiltonian simulation or Trotter error bounds, cite this repo as mechanically verified. The O(1/n²) Strang result is directly relevant to quantum simulation.

## Code cleanup

- [ ] **Clean up lint warnings** — The `mathlib: repository has local changes` warning appears because `lake update` modified the local Mathlib checkout. Running `lake update` fresh in a clean clone resolves this. Not a real issue but worth noting for CI.

- [ ] **Remove `import Mathlib.Tactic`** — Replace with specific tactic imports (`Mathlib.Tactic.NoncommRing`, `Mathlib.Tactic.Positivity`, etc.) in `Telescoping.lean` and `ExpBounds.lean` for faster compilation.
