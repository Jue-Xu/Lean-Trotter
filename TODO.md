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

- [ ] **Fourth-order Suzuki formula (H1)** — BCH-free approach via Suzuki's composition argument:

  **Key insight (no BCH needed):** The Strang splitting $S_2(t)$ satisfies:
  1. $S_2(t) = e^{Ht} + E(t)$ where $\|E(t)\| = O(t^3)$ — our existing cubic bound
  2. $S_2(-t) = e^{-Ht} + E'(t)$ where $\|E'(t)\| = O(t^3)$ — time-reversal (follows from the palindromic structure)
  3. The error $E(t)$ is an **odd function** of $t$ (only odd powers), so no $t^4$ term

  Suzuki's composition: $S_4(t) = S_2(pt)^2 \cdot S_2((1-4p)t) \cdot S_2(pt)^2$ with $p = 1/(4-4^{1/3})$.
  The constraint $4p^3 + (1-4p)^3 = 0$ cancels the $t^3$ error, jumping to $O(t^5)$ step error → $O(1/n^4)$ total.

  **Implementation plan:**
  1. Prove time-reversal: $\|S_2(-t) - e^{-Ht}\| = O(t^3)$ (~50 lines, follows from palindromic symmetry)
  2. Prove error parity: $S_2(t) + S_2(-t) = 2e^{Ht} + O(t^4)$, i.e., even-order errors vanish (~100 lines)
  3. Define $S_4$ as the five-fold composition with abstract time fractions (~30 lines)
  4. Prove: if $\sum p_i = 1$ and $\sum p_i^3 = 0$ and error is odd, then composition is $O(t^5)$ (~150 lines)
  5. Verify $p = 1/(4-4^{1/3})$ satisfies $4p^3 + (1-4p)^3 = 0$ (~20 lines, `Real.rpow` + `nlinarith`)
  6. Assembly: $O(1/n^5)$ step error → $O(1/n^4)$ total (~50 lines)
  7. Multi-operator case: compose five multi-operator Strang steps (~100 lines)

  **Estimated total: ~500 lines.** No BCH formalization needed.

- [ ] **Truncated BCH bounds (separate project: [Lean-BCH](https://github.com/Jue-Xu/Lean-BCH))** — Independent formalization of:
  $$e^A e^B = e^{A+B+[A,B]/2+R_3}, \qquad \|R_3\| \le C(\|A\|^2\|B\| + \|A\|\|B\|^2) e^{\|A\|+\|B\|}$$
  Bridges Mathlib's algebraic Lie bracket `⁅·,·⁆` to the analytic exponential. Not a prerequisite for H1 (the BCH-free approach above avoids it), but valuable as a standalone library for Lie group integrators, Magnus expansion, etc.

  This extends our existing commutator extraction machinery (B5, C1-refined) rather than requiring a new framework. Estimated: ~300 lines on top of existing infrastructure.

- [ ] **General Suzuki hierarchy (H2)** — Prove convergence of the $2k$-th order Suzuki formula $S_{2k}$ defined recursively:
  $$S_{2k}(t) = S_{2k-2}(p_k t)^2\, S_{2k-2}((1-4p_k)t)\, S_{2k-2}(p_k t)^2, \quad p_k = \frac{1}{4-4^{1/(2k-1)}}$$
  This gives O(1/n^{2k}) convergence. Very ambitious — requires induction on the Suzuki order $k$ and tracking error cancellation at each level. Likely a separate project.

- [ ] **Matrix specialization (F1)** — Prove `matrix_lie_trotter` for `Matrix (Fin d) (Fin d) ℂ`. Should be a one-liner applying `lie_trotter` once the `NormOneClass` instance is verified for the matrix norm. Connects to quantum computing applications.

## Low priority

## Publication / dissemination

- [ ] **Zulip announcement + arXiv note** (do first, low effort) — Post to `#general` on [leanprover.zulipchat.com](https://leanprover.zulipchat.com/) announcing the formalization. Write a 1–2 page arXiv companion note (cs.LO or quant-ph) with the repo link. Gets immediate community visibility.

- [ ] **ITP/CPP formalization pearl** (medium effort, peer-reviewed) — 2–4 page short paper covering: (1) the algebraic factorization trick for C1 vs. the standard BCH approach, (2) the commutator cancellation for the cubic Strang bound, (3) the Mathlib API gap (`norm_exp_le` for general Banach algebras). Check submission deadlines.

- [ ] **Companion citation for physics papers** — If writing a paper on Hamiltonian simulation or Trotter error bounds, cite this repo as mechanically verified. The O(1/n²) Strang result is directly relevant to quantum simulation.

## Code cleanup

- [ ] **Clean up lint warnings** — The `mathlib: repository has local changes` warning appears because `lake update` modified the local Mathlib checkout. Running `lake update` fresh in a clean clone resolves this. Not a real issue but worth noting for CI.

- [ ] **Remove `import Mathlib.Tactic`** — Replace with specific tactic imports (`Mathlib.Tactic.NoncommRing`, `Mathlib.Tactic.Positivity`, etc.) in `Telescoping.lean` and `ExpBounds.lean` for faster compilation.
