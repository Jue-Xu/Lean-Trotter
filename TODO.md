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

- [ ] **Multi-operator Lie-Trotter (G1)** — Generalize from $A+B$ to $A_1 + \cdots + A_m$:
  $$e^{A_1+\cdots+A_m} = \lim_{n\to\infty} (e^{A_1/n} \cdots e^{A_m/n})^n$$
  This is the version used in quantum simulation (Hamiltonians decompose into many terms).
  The proof generalizes by induction on $m$, peeling off one factor at a time:
  ```
  ‖e^{a₁}⋯e^{aₘ₊₁} - e^{a₁+⋯+aₘ₊₁}‖
    ≤ ‖e^{a₁}‖ · ‖e^{a₂}⋯e^{aₘ} - e^{a₂+⋯+aₘ}‖ + ‖e^{a₁}e^{a₂+⋯+aₘ} - e^{a₁+⋯+aₘ}‖
  ```
  Telescopes into a sum of pairwise C1-type bounds. Estimate: ~150 lines. Reuses all existing infrastructure.

- [ ] **Matrix specialization (F1)** — Prove `matrix_lie_trotter` for `Matrix (Fin d) (Fin d) ℂ`. Should be a one-liner applying `lie_trotter` once the `NormOneClass` instance is verified for the matrix norm. Connects to quantum computing applications.

## Low priority

## Publication / dissemination

- [ ] **Zulip announcement + arXiv note** (do first, low effort) — Post to `#general` on [leanprover.zulipchat.com](https://leanprover.zulipchat.com/) announcing the formalization. Write a 1–2 page arXiv companion note (cs.LO or quant-ph) with the repo link. Gets immediate community visibility.

- [ ] **ITP/CPP formalization pearl** (medium effort, peer-reviewed) — 2–4 page short paper covering: (1) the algebraic factorization trick for C1 vs. the standard BCH approach, (2) the commutator cancellation for the cubic Strang bound, (3) the Mathlib API gap (`norm_exp_le` for general Banach algebras). Check submission deadlines.

- [ ] **Companion citation for physics papers** — If writing a paper on Hamiltonian simulation or Trotter error bounds, cite this repo as mechanically verified. The O(1/n²) Strang result is directly relevant to quantum simulation.

## Code cleanup

- [ ] **Clean up lint warnings** — The `mathlib: repository has local changes` warning appears because `lake update` modified the local Mathlib checkout. Running `lake update` fresh in a clean clone resolves this. Not a real issue but worth noting for CI.

- [ ] **Remove `import Mathlib.Tactic`** — Replace with specific tactic imports (`Mathlib.Tactic.NoncommRing`, `Mathlib.Tactic.Positivity`, etc.) in `Telescoping.lean` and `ExpBounds.lean` for faster compilation.
