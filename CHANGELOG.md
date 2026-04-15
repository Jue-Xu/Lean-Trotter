# Changelog — Lie-Trotter Lean 4 Formalization

Lab notes: completed tasks, failed approaches, and key decisions.

---

## 2026-04-14: Commutator-scaling Trotter error via Duhamel formula

**What:** Proved the commutator-scaling bound from Childs et al. (2021), replacing the product `‖A‖‖B‖` with the commutator norm `‖[B,A]‖` in the Trotter error estimate.

**New file:** `LieTrotter/CommutatorScaling.lean` (370 lines, 0 sorry's)

**Key results:**
- `lie_trotter_integral_error`: integral representation of Trotter error via Duhamel/variation-of-parameters formula: $e^{tB}e^{tA} - e^{t(A+B)} = \int_0^t e^{(t-\tau)(A+B)}[e^{\tau B},A]e^{\tau A}d\tau$
- `exp_conj_sub_eq_integral`: commutator extraction via FTC on conjugation: $e^{\tau B}Ae^{-\tau B} - A = \int_0^\tau e^{sB}[B,A]e^{-sB}ds$
- `norm_lie_trotter_comm_scaling`: $\|e^{tB}e^{tA} - e^{t(A+B)}\| \le \|[B,A]\|t^2 e^{t(\|A\|+3\|B\|)}$

**Proof strategy:** FTC-2 via conjugation — define $w(\tau) = e^{-\tau(A+B)} e^{\tau B} e^{\tau A}$, compute $w'(\tau)$ via product rule, apply FTC-2. Avoids ODE uniqueness (Gronwall) entirely. Pull constant factor out of interval integral via `ContinuousLinearMap.intervalIntegral_comp_comm`.

**Infrastructure introduced:**
- `hasDerivAt_exp_conj`: derivative of $s \mapsto e^{sB}Ae^{-sB}$
- `hasDerivAt_conj_trotter`: derivative of $\tau \mapsto e^{-\tau(A+B)} e^{\tau B} e^{\tau A}$
- `norm_exp_conj_sub_le`, `norm_comm_exp_le`: commutator norm bounds via exponential conjugation

**Key design decisions:**
- Work over `NormedAlgebra ℝ 𝔸` directly (not general `𝕂`) to avoid `SMul ℝ 𝔸` instance synthesis failures
- Use `simp_rw` to normalize `(-u) • B` ↔ `u • (-B)` before applying `hasDerivAt_exp_smul_const'`
- Use `set E := exp(...)` + `Commute.exp_right` + `noncomm_ring` for algebraic simplification through opaque `exp` terms

**Known slack:** Bound has $t^2$ where paper has $t^2/2$ (tight). Tightening requires evaluating $\int_0^t \tau\,d\tau = t^2/2$ instead of constant bound $\int_0^t t\,d\tau = t^2$.

---

## 2026-03-30: Strang splitting O(1/n²) — complete (`edbd594`)

**What:** Proved symmetric Lie-Trotter (Strang splitting) converges at O(1/n²) rate.

**Key results:**
- `symmetric_lie_trotter`: `(exp(A/2n) exp(B/n) exp(A/2n))^n → exp(A+B)`
- `strang_error_rate_sq`: explicit O(1/n²) error bound
- `norm_exp_mul_exp_mul_exp_sub_exp_add_cubic`: cubic step error O(‖a‖²‖b‖ + ‖a‖‖b‖²)

**New infrastructure:**
- B5 (`norm_exp_remainder3_le`): third-order remainder `‖exp(a)-1-a-a²/2‖ ≤ ‖a‖³/6 · exp(‖a‖)`
- `norm_exp_mul_exp_sub_exp_add_sub_comm_le`: extract commutator [a,b]/2 from the Lie-Trotter error, bounding the remainder at cubic order
- `norm_exp_cross_tail_le`: bound `‖cross(x,y) - (xy+yx)/2‖` (degree ≥ 3 cross terms)

**Key insight:** In `exp(a)exp(b)exp(a) - exp(2a+b)`, the leading commutator `[a,b]` from `exp(a)·[exp(b),exp(a)]` cancels with the leading term of `E(2a,b)`. This leaves only cubic-order remainders, giving step error O(1/n³) and overall O(1/n²).

**Failed approaches:**
- Direct triple-product expansion (27 terms, unmanageable bookkeeping)
- `variable (𝕂) in` with doc comments (parser issues in Lean 4.29)
- `nlinarith` on complex coefficient bounds (needed explicit `mul_le_mul_of_nonneg_left` steps)
- `ring` for non-commutative identities (need `noncomm_ring`)

---

## 2026-03-29: Port to Lean 4.29.0-rc8 (`2afec17`)

**What:** Ported entire codebase from Lean 4.16.0 to 4.29.0-rc8 + latest Mathlib.

**API changes applied:**
- `exp 𝕂` → `exp` (NormedSpace.exp no longer takes field explicitly)
- `include 𝕂 in` before lemmas needing `𝕂` in proofs but not types
- `[NormOneClass 𝔸]` added to all section variables (required by `norm_pow_le`)
- `summable_of_nonneg_of_le h1 h2 h3` → `h3.of_nonneg_of_le h1 h2`
- `tsum_eq_zero_add h` → `h.tsum_eq_zero_add`
- `tsum_sub`, `tsum_le_tsum` → dot notation
- `nsmul_eq_smul_cast` → `Nat.cast_smul_eq_nsmul`
- `Real.exp_natMul` → `Real.exp_nat_mul`
- `∑ k in` → `∑ k ∈`
- `ring` → `noncomm_ring` for non-commutative identities
- `Mathlib.Order.Filter.AtTopBot` → `Mathlib.Order.Filter.AtTopBot.Basic`

**Failed approaches during port:**
- `variable (𝕂) in` before doc comments — silently breaks: `𝕂` not available in proof body. Root cause: `exp` no longer depends on `𝕂`, so Lean drops `𝕂` from the lemma even with `variable (𝕂) in`.
- `variable (𝕂) in` after doc comments — parser error: "unexpected token 'variable'; expected 'lemma'".
- **Fix that worked:** `include 𝕂 in` directly before the `/-- doc -/` line.

**Other issues encountered:**
- `two_mul_factorial_le` proof: `omega` can't handle `2 ≤ (n+2)*(n+1)` in newer Lean (non-linear). Fix: `nlinarith`.
- `simp [Nat.factorial]` closes goals that previously needed `simp only [...]; ring`. Some `ring` calls after `simp` became "no goals" errors.
- `Real.exp_eq_exp_ℝ` needed to bridge `NormedSpace.exp x` ↔ `Real.exp x` for real-valued tsum.
- `letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ 𝕂 𝔸` needed in `exp_div_pow` for `exp_nsmul`.

---

## 2026-03-29: Complete proof — 0 sorry's (`9a28787`)

**What:** Filled the final 3 sorry's:
1. `norm_exp_cross_term_le` — inductive power series bound + tsum assembly
2. `h_max` in Assembly — `norm_mul_le` + `norm_exp_le` + `Real.exp_add`
3. Final calc in Assembly — `exp(s/n)^n = exp(s)` via `Real.exp_natMul` + `field_simp`

**Key technique for C1 cross-term:** The inductive lemma
`‖(a+b)^m - a^m - b^m‖ ≤ (‖a‖+‖b‖)^m - ‖a‖^m - ‖b‖^m`
uses the algebraic identity (works in non-commutative rings):
`(a+b)^{m+1} - a^{m+1} - b^{m+1} = (a+b)((a+b)^m - a^m - b^m) + a·b^m + b·a^m`

---

## 2026-03-29: Fill sorry's for B, C, D tracks (`351291a`)

**What:** Reduced sorry count from 22 to 3 using parallel agent teams.

**Agents dispatched (in parallel):**
1. ExpBounds agent — B1-B4 (power series proofs)
2. ExpDivPow agent — D1 (4-line proof via `exp_nsmul`)
3. StepError agent — C1-C2 (algebraic factorization approach)

**B1-B4 proof technique:** All use the `exp_tsum_form` → `norm_tsum_le_tsum_norm` → `tsum_le_tsum` pipeline with `Real.hasSum_exp` for the real side. B3 uses the auxiliary `two_mul_factorial_le : 2·n! ≤ (n+2)!` for termwise comparison.

**Mathlib API gap found:** `‖exp a‖ ≤ exp ‖a‖` for general Banach algebras does NOT exist in Mathlib (only `Complex.norm_exp_le_exp_norm` for ℂ). We proved it from scratch.

---

## 2026-03-29: Restructure into modular files (`eb04fdb`)

**What:** Split 2 monolithic files (LieTrotter.lean, LieTrotterDetail.lean) into 5 modules under `LieTrotter/`. Consolidated best proofs, dropped abandoned attempts (3 incomplete telescoping variants). Sorry count: 22 → 9.

---

## 2026-03-29: Initial commit (`b35dba6`)

**What:** Created GitHub repo with initial proof structure. Telescoping (Track A) fully proved. All other tracks had sorry stubs with proof sketches.

**Repository:** https://github.com/Jue-Xu/Lean-Trotter (private)
