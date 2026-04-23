# Changelog — Lie-Trotter Lean 4 Formalization

Lab notes: completed tasks, failed approaches, and key decisions.

---

## 2026-04-23: Childs-heuristic axiom retired (axiom count 5 → 4)

**What:** Removed the `bch_childs_pointwise_residual` axiom that directly
encoded Childs 2021's heuristic coefficients 0.0047–0.0284. Replaced the
Level-1 bound `norm_suzuki4_childs_form_via_bch` with a new derivation
`norm_suzuki4_childs_form_via_level3` that composes the CAS-certified
Level 3 bound with the Lean-proved termwise inequality γᵢ ≤ αᵢ
(`bchTightPrefactors_le_childs`).

**Why:** Childs et al. 2021 themselves label those coefficients heuristic
("we do not have a rigorous proof of the tightness of these bounds"). The
Level-3 derivation delivers the same numerical bound from a strictly
stronger CAS-certified foundation, turning the Level-1 marketing claim
from "reproduces Childs's heuristic" to "reproduces Childs's bound from
an independently-tighter foundation."

**Impact:** Bound statement unchanged (`t⁵ · childsBoundSum`).
Axiom count 5 → 4. Build: 3353 jobs pass.

---

## 2026-04-23: Lean-BCH interface migration (axiom count 9 → 5)

**What:** Lean-BCH imported as git dependency at rev `61bf599`. Four
symmetric-BCH-cubic interface axioms (`symmetric_bch_cubic`,
`exp_symmetric_bch_cubic`, `norm_symmetric_bch_cubic_le`,
`norm_symmetric_bch_cubic_sub_smul_le`) replaced by theorems derived from
the corresponding Lean-BCH theorems specialized to `𝕂 := ℝ`.

**Constant bump:** scaling bound constant raised from axiomatized `10⁴`
to proven `2·10⁷`. Downstream `suzuki4_bchCubic_sum_bound`: `50000·s⁵`
→ `10⁸·s⁵`. Scope note: affects only Path-B roadmap composition theorem
(not yet wired), not the L1/L2/L3/L4 headline prefactors.

---

## 2026-04-22: Level 2 BCH-derived Childs-style bound

**What:** Added a rigorously BCH-derived 4th-order Trotter bound (Level 2)
that uses explicit unit coefficients on the 8 Childs 4-fold commutators,
in contrast to the Level 1 bound which axiomatizes Childs's heuristic
0.0047-0.0284 coefficients directly.

**New theorems (in `Suzuki4ViaBCH.lean`):**
- `bchFourFoldSum A B`: sum of 8 four-fold commutator norms, unit coefs.
- `bch_w4Deriv_quintic_level2` (axiom): primitive BCH pointwise residual
  `‖w4Deriv τ‖ ≤ 5 · bchFourFoldSum · τ⁴`, derived from `|βᵢ(Suzuki-p)| ≤ 1`
  for the BCH quintic expansion coefficients.
- `norm_suzuki4_level2_bch` (theorem): `‖S₄(t) - exp(tH)‖ ≤ t⁵ · bchFourFoldSum`.
- `childsBoundSum_le_bchFourFoldSum`: Level 2 dominates Level 1, confirming
  Level 2 is the weaker (rigorous) cousin.

**Level 1 vs Level 2 comparison:**
- Level 1 (`norm_suzuki4_childs_form_via_bch`): reproduces Childs et al.
  2021 Proposition pf4_bound_2term exactly with coefficients 0.0047-0.0284.
  Depends on `bch_childs_pointwise_residual` axiom which encodes Childs's
  heuristic balanced-factoring result.
- Level 2 (`norm_suzuki4_level2_bch`): weaker bound (unit coefficients),
  stronger derivation (primitive BCH axiom only). "Honest" BCH recovery.

---

## 2026-04-22: Option A Part 1 — BCH-derived Childs bound (Level 1)

**What:** Axiomatized the BCH-implied h4 identity and the Childs pointwise
residual, derived the unconditional S₄ O(t⁵) existence and the Childs-form
bound (matching Childs 2021 Proposition pf4_bound_2term exactly).

**New theorems (in `Suzuki4ViaBCH.lean`):**
- `bch_iteratedDeriv_s4Func_order4` (axiom): under IsSuzukiCubic,
  `iDer 4 (s4Func A B p) 0 = (A+B)^4`.
- `bch_iteratedDeriv_w4Func_order4_eq_zero`: w4Func order-4 vanishing
  derived via the Phase 5 bridge + proved h2, h3 + BCH h4 axiom.
- `norm_suzuki4_order5_via_bch_axiom`: existential S₄ O(t⁵) bound
  unconditional modulo the BCH h4 axiom.
- `bch_childs_pointwise_residual` (axiom): Childs-form pointwise residual.
- `norm_suzuki4_childs_form_via_bch`: Childs's exact 4th-order bound.

---

## 2026-04-21: Task 3 integration skeleton (Suzuki4ViaBCH)

**What:** Axiomatized minimal Lean-BCH interface (symmetric_bch_cubic +
3 theorems), proved `strangBlock_eq_exp_bchCubic` (each block as exp of
linear+cubic) and `suzuki4_bchCubic_sum_bound` (cubic sum over 5 blocks
is O(t⁵) under IsSuzukiCubic via Task 2's `4p³+(1-4p)³ = 0`).

**New file:** `LieTrotter/Suzuki4ViaBCH.lean`.

---

## 2026-04-21: Tasks 1 + 2 — Strang block decomposition and Suzuki cubic sum

**What:**
- Task 1 (`suzuki4Exp_eq_strangProduct`): S₄ factors as 5 symmetric Strang
  blocks with coefficients (p, p, 1-4p, p, p). Proved by merging 4 A-A
  junctions via `exp_add_of_commute`.
- Task 2 (`suzuki4_coeff_cube_sum_zero`): `4p³+(1-4p)³ = 0` under
  IsSuzukiCubic p.

**New file:** `LieTrotter/Suzuki4StrangBlocks.lean`.

---

## 2026-04-19: h3 PROVED UNCONDITIONALLY via factored-form identity

**What:** Proved `sumTripleCorr (s4DList A B p) = (4p³+(1-4p)³) · <op combo>`
as a pure operator-algebra identity (5-line tactic chain + `module`), then
derived h3 (`iteratedDeriv 3 (s4Func A B p) 0 = (A+B)^3`) under
`IsSuzukiCubic p`.

**New theorems (in `Suzuki4MultinomialExpand.lean`):**
- `sumTripleCorr_s4DList_eq_factored`
- `sumTripleCorr_s4DList_eq_zero`
- `iteratedDeriv_s4Func_order3_eq_cb`
- `iteratedDeriv_w4Func_order3_eq_zero`
- `norm_suzuki4_order5_with_h2_h3_and_w4Func_order4_vanishing`
  (strengthened CAPSTONE: only IsSuzukiCubic + w4Func order-4 vanishing needed)

Build: 3351 jobs, 0 sorries.

---

## 2026-04-15: Second-order Strang commutator-scaling — complete

**What:** Proved the commutator-scaling bound for the second-order Suzuki (Strang) formula, matching the Proposition in Childs et al. (2021), §VII.A:
$$\|S_2(t) - e^{tH}\| \le \frac{\|[B,[B,A]]\|}{12}t^3 + \frac{\|[A,[A,B]]\|}{24}t^3$$
for anti-Hermitian operators in C*-algebras, plus the multi-operator generalization.

**New files:**
- `LieTrotter/StrangCommutatorScaling.lean` (~480 lines, 0 sorry's)
- `LieTrotter/MultiStrangCommutatorScaling.lean` (~170 lines, 0 sorry's)

**Key results:**
- `hasDerivAt_conj_strang`: 4-factor product rule for $w(\tau) = e^{-\tau H} S_2(\tau)$
- `norm_strang_comm_scaling`: two-operator Strang commutator-scaling bound
- `norm_palindromicProd_sub_exp_sum_comm`: multi-operator generalization with `listDoubleCommNorm`

**Proof strategy:**
1. **4-factor product rule:** Factor the algebraic identity as $-(E \cdot (n_H + A' + A' + B) \cdot e_A \cdot e_B \cdot e_A) = 0$ via `noncomm_ring` + `abel`. Key fix: avoid duplicate `set A'` (causes `A'✝` shadowing) and normalize `(-τ)•(A+B) = τ•n_H` via `neg_smul`/`smul_neg`.
2. **"Subtract-constant-at-τ" trick:** Bounds the combined remainder $R_1 + \tau \cdot (\text{conj diff})$ without Fubini or integration-by-parts, using $\|H(s)-H(\tau)\| \le (\tau-s) C_A$.
3. **Anti-Hermitian isometry:** $\|e^{sX}\| = 1$ eliminates all exponential factors from the bound.
4. **Multi-operator induction:** Same pattern as `MultiCommutatorScaling.lean` — split into IH (bounded by isometry) + two-operator term (bounded by `norm_strang_comm_scaling`).

**Failed approaches:**
- Two-bracket decomposition (`strang_two_bracket_decomp` + separate `lie_trotter_integral_error` for each bracket): loses the O(τ) cancellation because the two integrals have different exponential weights. Must use the Duhamel integral (single integral of 𝒯₂) to get O(t³).
- `noncomm_ring` for the full 4-factor algebraic identity: fails because `noncomm_ring` can't handle commutativity relations `A'·e^{τA'} = e^{τA'}·A'` or integer smul coefficients `-2•x`. The fix: normalize associativity, then factor the free-ring difference as `(nH+A'+A'+B)·eA·eB·eA` which `noncomm_ring` CAN prove.
- `simp only [hcA]` (rewriting `A'·eA → eA·A'`): changes the direction needed for the free-ring factoring. Must NOT normalize commutativity before the `noncomm_ring` step.

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
