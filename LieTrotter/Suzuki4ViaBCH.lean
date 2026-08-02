/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# S₄ O(t⁵) via symmetric BCH composition (Path B integration skeleton)

This module provides the integration skeleton connecting **Lean-Trotter**'s
S₄ factorization (Task 1 in `Suzuki4StrangBlocks.lean`) with the **Lean-BCH**
symmetric BCH cubic theorems. It imports the Lean-BCH interface as thin
aliases (historically these were axiomatized inline), expresses each Strang
block via its BCH expansion, and sums the cubic terms, exploiting the
Suzuki cubic cancellation (Task 2).

## Path B outline

```
suzuki4Exp A B p t                                       [Task 1: s4Func_eq_strangProduct]
  = ∏ᵢ strangBlock A B (cᵢ·t)   for cᵢ ∈ {p,p,1-4p,p,p}

Each strangBlock A B (c·t) = exp((c·t)·A/2) · exp((c·t)·B) · exp((c·t)·A/2)
  = exp(c·t·(A+B) + E₃(c·t·A, c·t·B))                    [exp_symmetric_bch_cubic]
  = exp(c·t·(A+B) + c³·E₃(t·A, t·B) + R(c,t))            [norm_symmetric_bch_cubic_sub_smul_le]
  where ‖R(c,t)‖ ≤ 10⁴·|c|³·(t·(‖A‖+‖B‖))⁵

∑ᵢ cᵢ³ = 4p³ + (1-4p)³ = 0 under IsSuzukiCubic           [Task 2]

⟹ suzuki4Exp A B p t = exp(t·(A+B)) + O(t⁵) via telescoping.
```

## Status

- **Imported from Lean-BCH** (thin aliases / wrappers, formerly axioms):
  `symmetric_bch_cubic`, `exp_symmetric_bch_cubic`,
  `norm_symmetric_bch_cubic_le`, `norm_symmetric_bch_cubic_sub_smul_le`.
- **Proved:** `strangBlock_eq_exp_bchCubic` — reformulates Task 1's building
  block via the BCH interface.
- **Proved:** `suzuki4_bchCubic_sum_bound` — the sum of cubic BCH terms
  across the 5 Strang blocks is `O(t⁵)` under Suzuki.
- **Proved (formerly `bch_w4Deriv_*` axioms):**
  `bch_w4Deriv_quintic_level2`, `bch_w4Deriv_level3_tight`,
  `bch_uniform_integrated`, and `bch_iteratedDeriv_s4Func_order4`. Each
  composes a Lean-BCH bridge corollary with exp-Lipschitz / triangle-
  inequality lifts. See the top-of-file table in `CLAUDE.md` for the
  exact Lean-BCH dependency of each.

The full `norm_suzuki4_order5_via_strang_bch` theorem (telescoping + exp
composition) requires BCH-level composition estimates (multi-exp BCH).
Added as a conditional theorem taking the composition estimate as a
hypothesis — instantiated in a future file once the BCH multi-exp bound
is available.

## Compatibility

The thin aliases below mirror the exact statements in Lean-BCH's
`BCH/Basic.lean` (`symmetric_bch_cubic` definition, `exp_symmetric_bch`,
`norm_symmetric_bch_cubic_le`, `norm_symmetric_bch_cubic_sub_smul_le`).
The historical inline `axiom` declarations have been replaced by
`import BCH.Basic` + thin wrappers. The Lean-BCH pin `05e8c52`
(2026-07-28) makes both the quintic and septic imported chains
project-axiom-free.
-/

import LieTrotter.Suzuki4StrangBlocks
import LieTrotter.Suzuki4MultinomialExpand
import LieTrotter.Suzuki4ChildsForm
import LieTrotter.Suzuki4Module4
import LieTrotter.Suzuki4Phase5
import LieTrotter.Suzuki4BchBound
import LieTrotter.TaylorMatch
import BCH.Basic
import BCH.ChildsBasis
import BCH.Suzuki5Quintic

noncomputable section

open NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## Lean-BCH interface (imported from `BCH.Basic`)

The symmetric BCH cubic coefficient, its cubic norm bound, the `exp`
composition formula, and the quintic scaling bound are all imported from
Lean-BCH (specialized to `𝕂 := ℝ`). Previously these were axiomatized in
this file; they are now theorems derived from `BCH.symmetric_bch_cubic ℝ`,
`BCH.norm_symmetric_bch_cubic_le`, `BCH.exp_symmetric_bch`, and
`BCH.norm_symmetric_bch_cubic_sub_smul_le`.
-/

/-- **[IMPORTED from Lean-BCH]** Alias for `BCH.symmetric_bch_cubic ℝ`:
  the degree-3 part of `bch(bch(a/2,b), a/2)`, defined so that
  `bch(bch(a/2,b), a/2) = (a+b) + symmetric_bch_cubic a b + O(‖a‖+‖b‖)⁵`. -/
def symmetric_bch_cubic (a b : 𝔸) : 𝔸 :=
  BCH.symmetric_bch_cubic ℝ a b

/-- **[IMPORTED from Lean-BCH]** `exp(a/2)·exp(b)·exp(a/2) = exp((a+b) + E₃(a,b))`
  for `‖a‖+‖b‖ < 1/4`. Combines `BCH.exp_symmetric_bch` with the
  definition of `symmetric_bch_cubic`. -/
theorem exp_symmetric_bch_cubic (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    exp ((1 / 2 : ℝ) • a) * exp b * exp ((1 / 2 : ℝ) • a) =
    exp ((a + b) + symmetric_bch_cubic a b) := by
  unfold symmetric_bch_cubic BCH.symmetric_bch_cubic
  have hhalf : ((1 / 2 : ℝ)) = ((2 : ℝ)⁻¹) := by norm_num
  rw [show ((a + b) + (BCH.bch (𝕂 := ℝ) (BCH.bch (𝕂 := ℝ) ((2 : ℝ)⁻¹ • a) b)
              ((2 : ℝ)⁻¹ • a) - (a + b))) =
        BCH.bch (𝕂 := ℝ) (BCH.bch (𝕂 := ℝ) ((2 : ℝ)⁻¹ • a) b) ((2 : ℝ)⁻¹ • a)
        from by abel]
  rw [hhalf]
  exact (BCH.exp_symmetric_bch (𝕂 := ℝ) a b hab).symm

/-- **[IMPORTED from Lean-BCH]** Cubic norm bound:
  `‖E₃(a,b)‖ ≤ 300·(‖a‖+‖b‖)³`. -/
theorem norm_symmetric_bch_cubic_le (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    ‖symmetric_bch_cubic a b‖ ≤ 300 * (‖a‖ + ‖b‖) ^ 3 :=
  BCH.norm_symmetric_bch_cubic_le (𝕂 := ℝ) a b hab

/-- **[IMPORTED from Lean-BCH]** Scaling bound:
  `‖E₃(c·a, c·b) - c³·E₃(a,b)‖ ≤ 2·10⁷·|c|³·(‖a‖+‖b‖)⁵` for `|c|≤1`.
  Encodes the degree-3 homogeneity of `symmetric_bch_cubic` modulo a
  quintic remainder. Key to Suzuki's order-4 cancellation.

  The constant `2·10⁷` comes from Lean-BCH's rigorous triangle-inequality
  proof; the previous axiomatized constant `10⁴` was speculative and
  tighter than what the current Lean-BCH proof delivers.

  **Scope of the 2·10⁷ constant:** this bound (and its downstream
  `suzuki4_bchCubic_sum_bound` with constant `10⁸`) feeds ONLY the
  Path-B roadmap theorem `norm_suzuki4_order5_via_strang_bch` (multi-exp
  composition, not yet wired up). **It does NOT affect the L1/L2/L3/L4
  headline Trotter error bounds** (`norm_suzuki4_childs_form_via_level3`,
  `norm_suzuki4_level2_bch`, `norm_suzuki4_level3_bch`,
  `norm_suzuki4_level4_uniform`), which derive their prefactors from the
  separate `bch_w4Deriv_*` theorems (formerly axioms) encoding pointwise
  residuals on the full 5-factor product. -/
theorem norm_symmetric_bch_cubic_sub_smul_le (a b : 𝔸) (c : ℝ)
    (hc : |c| ≤ 1) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    ‖symmetric_bch_cubic (c • a) (c • b) - c ^ 3 • symmetric_bch_cubic a b‖ ≤
      20000000 * |c| ^ 3 * (‖a‖ + ‖b‖) ^ 5 := by
  have h := BCH.norm_symmetric_bch_cubic_sub_smul_le (𝕂 := ℝ) a b c hc hab
  -- In NormedAlgebra ℝ 𝔸, (↑c : ℝ) = c, so the coerced smul equals ordinary smul.
  -- ℝ^3 smul of ℝ-valued quantity is the same numeric expression.
  simpa [symmetric_bch_cubic] using h

/-!
## Strang block via BCH

Reformulate each Strang block in the S₄ factorization through the
symmetric BCH cubic.
-/

/-- **Strang block = exp(linear + E₃)**: for `‖s·A‖+‖s·B‖ < 1/4`,
  `strangBlock A B s = exp(s·(A+B) + E₃(s·A, s·B))`.

Uses `exp_symmetric_bch_cubic` with `a = s•A`, `b = s•B`, and the
identities `(s/2)•A = (1/2)•(s•A)` and `s•A + s•B = s•(A+B)`. -/
theorem strangBlock_eq_exp_bchCubic (A B : 𝔸) (s : ℝ)
    (hs : ‖s • A‖ + ‖s • B‖ < 1 / 4) :
    strangBlock A B s = exp (s • (A + B) + symmetric_bch_cubic (s • A) (s • B)) := by
  unfold strangBlock
  have hhalf : ∀ (X : 𝔸), (s / 2 : ℝ) • X = (1 / 2 : ℝ) • (s • X) := by
    intros X; rw [smul_smul]; congr 1; ring
  simp only [hhalf]
  rw [exp_symmetric_bch_cubic (s • A) (s • B) hs, smul_add]

/-!
## Sum of cubic BCH terms across the 5 Strang blocks

Under `IsSuzukiCubic p`, the degree-3 parts of the 5 Strang blocks sum to
zero (modulo an `O(t⁵)` remainder). This is the key cancellation enabling
order-4 convergence.
-/

/-- **Key quintic bound**: the sum of cubic BCH coefficients over the 5
  Strang blocks is `O(t⁵)` under IsSuzukiCubic.

  For `cᵢ ∈ {p, p, 1-4p, p, p}` and `|cᵢ|·t·(‖A‖+‖B‖) < 1/4`:
  ```
  ‖∑ᵢ E₃(cᵢ·t·A, cᵢ·t·B)‖
    ≤ ‖(∑ cᵢ³)·E₃(tA, tB)‖ + ∑‖E₃(cᵢ·tA, cᵢ·tB) - cᵢ³·E₃(tA, tB)‖
    ≤ 0 + 5·2·10⁷·max|cᵢ|³·(t·(‖A‖+‖B‖))⁵
  ```
  The `(∑ cᵢ³)·E₃` term vanishes by `suzuki4_coeff_cube_sum_zero` (Task 2);
  the per-block residual is bounded by `norm_symmetric_bch_cubic_sub_smul_le`
  (derived from `BCH.norm_symmetric_bch_cubic_sub_smul_le`, constant 2·10⁷). -/
theorem suzuki4_bchCubic_sum_bound (A B : 𝔸) (p : ℝ) (hcubic : IsSuzukiCubic p)
    (hp : |p| ≤ 1) (hq : |1 - 4 * p| ≤ 1) (t : ℝ) (ht_nn : 0 ≤ t)
    (ht : t * (‖A‖ + ‖B‖) < 1 / 4) :
    ‖symmetric_bch_cubic ((p : ℝ) • (t • A)) ((p : ℝ) • (t • B)) +
      symmetric_bch_cubic ((p : ℝ) • (t • A)) ((p : ℝ) • (t • B)) +
      symmetric_bch_cubic (((1 - 4 * p) : ℝ) • (t • A)) (((1 - 4 * p) : ℝ) • (t • B)) +
      symmetric_bch_cubic ((p : ℝ) • (t • A)) ((p : ℝ) • (t • B)) +
      symmetric_bch_cubic ((p : ℝ) • (t • A)) ((p : ℝ) • (t • B))‖ ≤
      100000000 * (t * (‖A‖ + ‖B‖)) ^ 5 := by
  -- Set up norms
  set s := ‖t • A‖ + ‖t • B‖ with hs_def
  have hAB_nn : 0 ≤ ‖A‖ + ‖B‖ := by positivity
  have hs_eq : s = t * (‖A‖ + ‖B‖) := by
    rw [hs_def, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_nn]; ring
  have hs_lt : s < 1 / 4 := by rw [hs_eq]; exact ht
  -- Residuals and their bounds from the BCH theorem
  set E₃ab : 𝔸 := symmetric_bch_cubic (t • A) (t • B) with hE₃ab_def
  set Rp : 𝔸 := symmetric_bch_cubic (p • (t • A)) (p • (t • B)) - p ^ 3 • E₃ab with hRp_def
  set Rq : 𝔸 := symmetric_bch_cubic ((1 - 4 * p) • (t • A)) ((1 - 4 * p) • (t • B)) -
                (1 - 4 * p) ^ 3 • E₃ab with hRq_def
  -- Per-block residuals: ‖R_c‖ ≤ 2·10⁷·|c|³·s⁵
  have hRp_bd : ‖Rp‖ ≤ 20000000 * |p| ^ 3 * s ^ 5 := by
    rw [hRp_def]; exact norm_symmetric_bch_cubic_sub_smul_le (t • A) (t • B) p hp hs_lt
  have hRq_bd : ‖Rq‖ ≤ 20000000 * |1 - 4 * p| ^ 3 * s ^ 5 := by
    rw [hRq_def]; exact norm_symmetric_bch_cubic_sub_smul_le (t • A) (t • B) (1 - 4 * p) hq hs_lt
  -- Key abel identity: each E₃(c•a, c•b) = c³ • E₃ab + R_c, so the sum rearranges
  -- into (Σcᵢ³) • E₃ab + (sum of residuals). The Σcᵢ³=0 part vanishes by Suzuki.
  have hcube_sum : p ^ 3 + p ^ 3 + (1 - 4 * p) ^ 3 + p ^ 3 + p ^ 3 = 0 :=
    suzuki4_coeff_cube_sum_zero p hcubic
  have hkey : symmetric_bch_cubic (p • (t • A)) (p • (t • B)) +
      symmetric_bch_cubic (p • (t • A)) (p • (t • B)) +
      symmetric_bch_cubic ((1 - 4 * p) • (t • A)) ((1 - 4 * p) • (t • B)) +
      symmetric_bch_cubic (p • (t • A)) (p • (t • B)) +
      symmetric_bch_cubic (p • (t • A)) (p • (t • B)) =
      (p ^ 3 + p ^ 3 + (1 - 4 * p) ^ 3 + p ^ 3 + p ^ 3) • E₃ab +
      (Rp + Rp + Rq + Rp + Rp) := by
    rw [hRp_def, hRq_def]
    simp only [add_smul]; abel
  rw [hkey, hcube_sum, zero_smul, zero_add]
  -- Each |cᵢ|³ ≤ 1, so each residual ≤ 2·10⁷·s⁵
  have hp3_le : |p| ^ 3 ≤ 1 := by
    calc |p| ^ 3 ≤ 1 ^ 3 := pow_le_pow_left₀ (abs_nonneg p) hp 3
      _ = 1 := one_pow 3
  have hq3_le : |1 - 4 * p| ^ 3 ≤ 1 := by
    calc |1 - 4 * p| ^ 3 ≤ 1 ^ 3 :=
      pow_le_pow_left₀ (abs_nonneg _) hq 3
      _ = 1 := one_pow 3
  have hs_nn : 0 ≤ s := by rw [hs_eq]; positivity
  have hs5_nn : 0 ≤ s ^ 5 := pow_nonneg hs_nn 5
  have hRp_le : ‖Rp‖ ≤ 20000000 * s ^ 5 := by
    calc ‖Rp‖ ≤ 20000000 * |p| ^ 3 * s ^ 5 := hRp_bd
      _ ≤ 20000000 * 1 * s ^ 5 := by gcongr
      _ = 20000000 * s ^ 5 := by ring
  have hRq_le : ‖Rq‖ ≤ 20000000 * s ^ 5 := by
    calc ‖Rq‖ ≤ 20000000 * |1 - 4 * p| ^ 3 * s ^ 5 := hRq_bd
      _ ≤ 20000000 * 1 * s ^ 5 := by gcongr
      _ = 20000000 * s ^ 5 := by ring
  -- Triangle inequality: ‖∑ Rᵢ‖ ≤ ∑ ‖Rᵢ‖ ≤ 5·2·10⁷·s⁵ = 10⁸·s⁵
  calc ‖Rp + Rp + Rq + Rp + Rp‖
      ≤ ‖Rp‖ + ‖Rp‖ + ‖Rq‖ + ‖Rp‖ + ‖Rp‖ := by
        calc _ ≤ ‖Rp + Rp + Rq + Rp‖ + ‖Rp‖ := norm_add_le _ _
          _ ≤ ‖Rp + Rp + Rq‖ + ‖Rp‖ + ‖Rp‖ := by
              gcongr; exact norm_add_le _ _
          _ ≤ ‖Rp + Rp‖ + ‖Rq‖ + ‖Rp‖ + ‖Rp‖ := by
              gcongr; exact norm_add_le _ _
          _ ≤ ‖Rp‖ + ‖Rp‖ + ‖Rq‖ + ‖Rp‖ + ‖Rp‖ := by
              gcongr; exact norm_add_le _ _
    _ ≤ 20000000 * s ^ 5 + 20000000 * s ^ 5 + 20000000 * s ^ 5 +
        20000000 * s ^ 5 + 20000000 * s ^ 5 := by linarith
    _ = 100000000 * s ^ 5 := by ring
    _ = 100000000 * (t * (‖A‖ + ‖B‖)) ^ 5 := by rw [hs_eq]

/-!
## Roadmap: full Path B integration theorem

The main theorem `norm_suzuki4_order5_via_strang_bch` would conclude:
```
∃ C ≥ 0, ‖suzuki4Exp A B p t - exp(t•(A+B))‖ ≤ C·t⁵
```
given `IsSuzukiCubic p` and `t·(‖A‖+‖B‖) < 1/4`.

**Proof outline (future work):**
1. `suzuki4Exp_eq_strangProduct` (Task 1) ⟹ product of 5 Strang blocks.
2. `strangBlock_eq_exp_bchCubic` for each block ⟹ each block is
   `exp(cᵢ·t·(A+B) + E₃(cᵢ·t·A, cᵢ·t·B))`.
3. Multi-exp composition (telescoping, as in `Suzuki4OrderFive.lean`):
   reduce `Π exp(Xᵢ) - exp(∑ Xᵢ)` to a sum of commutator corrections.
4. `suzuki4_bchCubic_sum_bound` bounds the cubic-term sum by `O(t⁵)`.
5. Cross-commutator corrections from step 3 combine with the residuals
   to give the `C·t⁵` bound.

Step 3 requires a multi-exp BCH composition estimate, which is the main
missing piece on the Trotter side. It can likely be derived from the
existing `CommutatorScaling.lean` infrastructure plus `norm_exp_le`.
-/

/-!
## Shortcut path: BCH-implied h4 ⟹ unconditional Childs-form bound

The full composition bound in the roadmap above is substantial; a shorter
route to the S₄ O(t⁵) result is the single BCH consequence we actually need
for the existing CAPSTONE: the order-4 vanishing of
`iteratedDeriv (s4Func A B p) at 0`.

Mathematical justification:

For Suzuki palindromic p, the BCH log of `s4Func(τ)` has only odd τ-powers:
  `log(s4Func(τ)) = τ·H + τ³·R₃ + τ⁵·R₅ + O(τ⁷)`
Under `IsSuzukiCubic p` (which is the defining Suzuki order-4 condition),
`R₃ = 0`. Hence `s4Func(τ) = exp(τ·H + τ⁵·R₅ + O(τ⁷))`. Taylor expansion
of `exp` gives `τ⁴` coefficient of `s4Func(τ)` equal to `H⁴/24`, so
`iteratedDeriv 4 (s4Func A B p) 0 = 4!·(H⁴/24) = H⁴ = (A+B)⁴`.

This is exactly the h4 identity, now a Lean theorem
`bch_iteratedDeriv_s4Func_order4` via the SLICE 1+2+3 chain (single-step
BCH O(|τ|⁵) bound + generic Taylor-match-from-norm + the Mathlib identity
`iteratedDeriv_exp_smul_mul_at_zero`).
-/

/-- **[THEOREM (was axiom)]** For Suzuki palindromic `p`, the 4th iterated
  derivative of `s4Func` at `τ = 0` equals `(A+B)^4`.

  **Proof**: derived from
  - SLICE 1: the single-step O(|τ|⁵) BCH bound
    `exists_norm_s4Func_sub_exp_le_t5 A B p hcubic`
    (in `LieTrotter/Suzuki4BchBound.lean`, itself an application of BCH
    M2b + M4b + exp-Lipschitz).
  - SLICE 2: the Taylor-match-from-norm lemma
    `iteratedDeriv_eq_of_norm_le_pow` (in `LieTrotter/TaylorMatch.lean`).
  - The standard identity
    `iteratedDeriv k (fun τ => exp(τ•X)) 0 = X^k`
    (via `iteratedDeriv_exp_smul_mul_at_zero` with `c = 1`).

  Under `IsSuzukiCubic p`, BCH gives `s4Func(τ) = exp(τH) + O(τ⁵)` in a
  neighborhood of 0. The Taylor-match lemma converts the O(τ⁵) bound
  into equality of the first five iterated derivatives at 0. The 4th
  iterated derivative of `exp(τH)` at 0 is `H^4 = (A+B)^4`. -/
theorem bch_iteratedDeriv_s4Func_order4
    (A B : 𝔸) (p : ℝ) (hcubic : IsSuzukiCubic p) :
    iteratedDeriv 4 (s4Func A B p) 0 = (A + B) ^ 4 := by
  -- SLICE 1: single-step O(|τ|⁵) bound on s4Func - exp(τ•(A+B)).
  obtain ⟨δ, hδ_pos, C, _hC_nn, h_bound⟩ :=
    exists_norm_s4Func_sub_exp_le_t5 A B p hcubic
  -- ContDiff for both sides: s4Func and τ ↦ exp(τ•(A+B)).
  have hCD_s4 : ContDiff ℝ 4 (s4Func A B p) := contDiff_s4Func A B p
  have h_exp_fun_eq :
      (fun τ : ℝ => exp (τ • (A + B))) = fun τ : ℝ => exp ((1 * τ) • (A + B)) := by
    funext τ; rw [one_mul]
  have hCD_exp : ContDiff ℝ 4 (fun τ : ℝ => exp (τ • (A + B))) := by
    rw [h_exp_fun_eq]
    exact contDiff_iff_contDiffAt.mpr fun x =>
      contDiffAt_exp_smul_mul (A + B) 1 x
  -- SLICE 2: Taylor-match at order 4.
  have h_match := iteratedDeriv_eq_of_norm_le_pow hCD_s4 hCD_exp hδ_pos h_bound 4 le_rfl
  -- Standard identity: iteratedDeriv 4 (fun τ => exp(τ•V)) 0 = V^4.
  have h_exp_iter :
      iteratedDeriv 4 (fun τ : ℝ => exp (τ • (A + B))) 0 = (A + B) ^ 4 := by
    rw [h_exp_fun_eq, iteratedDeriv_exp_smul_mul_at_zero, one_smul]
  rw [h_exp_iter] at h_match
  exact h_match

/-- **w4Func order-4 vanishing from BCH** (given Suzuki):
  `iteratedDeriv 4 (w4Func A B p) 0 = 0`.

  Combines the proved BCH h4 theorem with the Phase 5 bridge
  `iteratedDeriv_w4Func_order4_zero_iff_of_order23` and our proved
  h2, h3 (where h3 needs IsSuzukiCubic). -/
theorem bch_iteratedDeriv_w4Func_order4_eq_zero
    (A B : 𝔸) (p : ℝ) (hcubic : IsSuzukiCubic p) :
    iteratedDeriv 4 (w4Func A B p) 0 = 0 := by
  have h2 := iteratedDeriv_s4Func_order2_eq_sq A B p
  have h3 := iteratedDeriv_s4Func_order3_eq_cb A B p hcubic
  have h4 := bch_iteratedDeriv_s4Func_order4 A B p hcubic
  exact (iteratedDeriv_w4Func_order4_zero_iff_of_order23 A B p h2 h3).mpr h4

/-!
## Unconditional S₄ O(t⁵) via the BCH theorem

With `bch_iteratedDeriv_s4Func_order4` in hand, the strengthened CAPSTONE
from `Suzuki4MultinomialExpand.lean` closes without any derivative-level
hypotheses — only `IsSuzukiCubic p` and the anti-Hermitian structure.
-/

section AntiHermitian

variable [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]

/-- **S₄ O(t⁵) from BCH**: unconditional via the proved BCH h4 theorem. -/
theorem norm_suzuki4_order5_via_bch_axiom (A B : 𝔸)
    (hA : star A = -A) (hB : star B = -B) (p : ℝ) (hcubic : IsSuzukiCubic p)
    {t : ℝ} (ht : 0 < t) :
    ∃ C ≥ 0, ∀ τ ∈ Set.Icc (0 : ℝ) t,
      ‖suzuki4Exp A B p τ - exp (τ • (A + B))‖ ≤ C * τ ^ 5 :=
  norm_suzuki4_order5_with_h2_h3_and_w4Func_order4_vanishing
    A B hA hB p hcubic ht (bch_iteratedDeriv_w4Func_order4_eq_zero A B p hcubic)

/-!
## Level 2: Explicit BCH-derived 4-fold commutator bound

Childs et al. (2021), arXiv Proposition J.1, states:
```
  ‖S₄(t) - exp(tH)‖ ≤ t⁵ · Σ αᵢ · ‖Cᵢ‖   (8 four-fold commutators)
```
with specific coefficients `α₁...α₈ ∈ [0.0046, 0.0284]`.

The proposition is rigorous; the paper notes that the tightness of its
coefficients is not proved. A separate BCH derivation gives the
unit-coefficient bound
```
  ‖S₄(t) - exp(tH)‖ ≤ M_bch · t⁵ · Σᵢ ‖Cᵢ‖
```
where `M_bch` is a BCH-derived constant.

### The BCH-derived constant

Under `IsSuzukiCubic p`, the BCH log-expansion of `s4Func(τ)` has the form
```
  log(s4Func(τ)) = τH + τ⁵·R₅ + O(τ⁷)     (odd powers only, cubic cancels)
```
with `R₅` a specific linear combination of 4-fold nested commutators in
`A, B`. Expanding `R₅` in the 8 Childs commutator basis
`{childsComm₁, …, childsComm₈}` gives
```
  R₅ = Σᵢ βᵢ(p) · Cᵢ
```
with `βᵢ` rational functions of `p`. For Suzuki `p = 1/(4-4^(1/3))`, each
`|βᵢ|` is bounded by an explicit constant `M_bch ≥ max_i |βᵢ|`.

The value `M_bch = 1` (our choice below) is a crude but explicit bound:
each `βᵢ(p)` for Suzuki `p` satisfies `|βᵢ| ≤ 1` by direct evaluation of
the rational expressions. Tighter constants (e.g., Childs's 0.0046–0.0284)
require extra algebraic simplification beyond raw BCH.
-/

/-- Sum of the 8 Childs 4-fold commutator norms with **unit coefficients**
  (Level 2 BCH bound). Compare to `childsBoundSum` which uses Childs's
  published 4-decimal coefficients. -/
def bchFourFoldSum (A B : 𝔸) : ℝ :=
  ‖childsComm₁ A B‖ + ‖childsComm₂ A B‖ + ‖childsComm₃ A B‖ + ‖childsComm₄ A B‖ +
  ‖childsComm₅ A B‖ + ‖childsComm₆ A B‖ + ‖childsComm₇ A B‖ + ‖childsComm₈ A B‖

omit [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] in
lemma bchFourFoldSum_nonneg (A B : 𝔸) : 0 ≤ bchFourFoldSum A B := by
  unfold bchFourFoldSum; positivity

/-- Childs's sum dominates unit sum times max Childs coefficient; trivially
  the unit sum `bchFourFoldSum` dominates Childs's `childsBoundSum`
  (all Childs coefficients are `< 1`). -/
lemma childsBoundSum_le_bchFourFoldSum (A B : 𝔸) :
    childsBoundSum A B ≤ bchFourFoldSum A B := by
  unfold childsBoundSum bchFourFoldSum
  -- Each 0.00XX coefficient is ≤ 1
  have hC1 := norm_nonneg (childsComm₁ A B)
  have hC2 := norm_nonneg (childsComm₂ A B)
  have hC3 := norm_nonneg (childsComm₃ A B)
  have hC4 := norm_nonneg (childsComm₄ A B)
  have hC5 := norm_nonneg (childsComm₅ A B)
  have hC6 := norm_nonneg (childsComm₆ A B)
  have hC7 := norm_nonneg (childsComm₇ A B)
  have hC8 := norm_nonneg (childsComm₈ A B)
  nlinarith

omit [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] in
/-- **Level 2 BCH τ⁵ identification (primitive bound)**. Under
  `IsSuzukiCubic p`, there exist `δ > 0` and `K ≥ 0` such that for all
  `τ ∈ [0, δ)`,
```
  ‖suzuki5_bch ℝ A B p τ − τ • (A + B)‖ ≤
    τ⁵ · bchFourFoldSum A B + K · τ⁶
```
  where `suzuki5_bch = log(S₄(τ))`, `bchFourFoldSum = Σᵢ ‖Cᵢ‖` over the
  8 Childs 4-fold commutators with **unit coefficients**, and the
  `K·τ⁶` term encapsulates higher-order BCH corrections.

  **Now a theorem (was an axiom).** Derived directly from Lean-BCH's
  bridge corollary `BCH.suzuki5_log_product_quintic_of_IsSuzukiCubic`.
  At the current Lean-BCH pin `05e8c52`, the upstream B1.c quintic
  assumption (`BCH.symmetric_bch_quintic_sub_poly_axiom`) that underwrote the
  bridge has a proved replacement, so `#print axioms bch_w4Deriv_quintic_level2`
  reports only the standard Lean foundational axioms
  `[propext, Classical.choice, Quot.sound]`. -/
theorem bch_w4Deriv_quintic_level2
    (A B : 𝔸) (p : ℝ) (hcubic : IsSuzukiCubic p) :
    ∃ δ > (0 : ℝ), ∃ K ≥ (0 : ℝ), ∀ τ : ℝ, 0 ≤ τ → τ < δ →
      ‖BCH.suzuki5_bch ℝ A B p τ - τ • (A + B)‖ ≤
        τ ^ 5 * BCH.bchFourFoldSum A B + K * τ ^ 6 :=
  BCH.suzuki5_log_product_quintic_of_IsSuzukiCubic A B p hcubic

omit [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] in
/-- **Level 2 BCH-derived Trotter bound**: under `IsSuzukiCubic p`, the
  Suzuki S₄ product approximates `exp(t•(A+B))` to order `t⁵` on a
  neighborhood of zero:
```
  ‖S₄(t) - exp(t•(A+B))‖ ≤ C · t⁵        for t ∈ [0, δ)
```
  The theorem type records only `C·t⁵`; the proof constructs `C` from the
  unit-coefficient `bchFourFoldSum A B` and an exp-Lipschitz factor. Use
  `norm_suzuki4_level2_explicit` to retain the unit sum in the statement.

  Derivation: combine `bch_w4Deriv_quintic_level2`
  (τ⁵ identification of `log S₄(τ)`) with the M2b round-trip
  `BCH.exp_suzuki5_bch` (`S₄(τ) = exp(suzuki5_bch τ)` in the
  small-coefficient regime) and exp-Lipschitz `BCH.norm_exp_add_sub_exp_le`.

  Replacing the unit sum by the certified γᵢ leading coefficients is
  `norm_suzuki4_level3_explicit`, via
  `bch_w4Deriv_level3_tight`. -/
theorem norm_suzuki4_level2_bch (A B : 𝔸)
    (p : ℝ) (hcubic : IsSuzukiCubic p) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ τ : ℝ, 0 ≤ τ → τ < δ →
      ‖suzuki4Exp A B p τ - exp (τ • (A + B))‖ ≤ C * τ ^ 5 := by
  -- Extract (δ_log, K) from the Lean-BCH τ⁵ identification.
  obtain ⟨δ_log, hδ_log_pos, K, hK_nn, h_log_bound⟩ :=
    bch_w4Deriv_quintic_level2 A B p hcubic
  -- We also need the small-coefficient regime for M2b round-trip.
  have h_regime := exists_regime_nhds A B p
  rw [Metric.eventually_nhds_iff] at h_regime
  obtain ⟨δ_reg, hδ_reg_pos, h_regime⟩ := h_regime
  -- Shrink δ to ensure τ ≤ 1 so the exp factor is bounded uniformly.
  set δ := min δ_log (min δ_reg 1) with hδ_def
  have hδ_pos : 0 < δ := lt_min hδ_log_pos (lt_min hδ_reg_pos (by norm_num : (0:ℝ) < 1))
  have hδ_le_log : δ ≤ δ_log := min_le_left _ _
  have hδ_le_reg : δ ≤ δ_reg := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ_le_one : δ ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
  -- Define explicit C: (bchFourFoldSum + K) · exp(‖A+B‖ + bchFourFoldSum + K).
  set Sfs := BCH.bchFourFoldSum A B with hSfs_def
  have hSfs_nn : 0 ≤ Sfs := by
    show (0:ℝ) ≤ BCH.bchFourFoldSum A B
    exact BCH.bchFourFoldSum_nonneg A B
  set C := (Sfs + K) * Real.exp (‖A + B‖ + Sfs + K) with hC_def
  have hC_nn : 0 ≤ C := by
    refine mul_nonneg (add_nonneg hSfs_nn hK_nn) (Real.exp_pos _).le
  refine ⟨δ, hδ_pos, C, hC_nn, ?_⟩
  intro τ hτ_nn hτ_lt
  -- Pointwise regime + log bound at this τ.
  have hτ_lt_log : τ < δ_log := lt_of_lt_of_le hτ_lt hδ_le_log
  have hτ_lt_reg : τ < δ_reg := lt_of_lt_of_le hτ_lt hδ_le_reg
  have hτ_le_one : τ ≤ 1 := le_trans hτ_lt.le hδ_le_one
  have hτ_dist : dist τ 0 < δ_reg := by rw [Real.dist_eq]; simpa [abs_of_nonneg hτ_nn] using hτ_lt_reg
  obtain ⟨h_R, _h_pτ, _h_1m4pτ, _h_regsb, _h_Zbch, _h_nested⟩ := h_regime hτ_dist
  have h_log := h_log_bound τ hτ_nn hτ_lt_log
  -- M2b round-trip: S₄(τ) = exp(suzuki5_bch τ).
  have h_exp_bch : exp (BCH.suzuki5_bch ℝ A B p τ) = BCH.suzuki5Product (𝕂 := ℝ) A B p τ :=
    BCH.exp_suzuki5_bch (𝕂 := ℝ) A B p τ h_R
  -- Write suzuki5_bch = τ•(A+B) + δ_bch where δ_bch := suzuki5_bch - τ•(A+B).
  set δ_bch := BCH.suzuki5_bch ℝ A B p τ - τ • (A + B) with hδ_bch_def
  have h_add : τ • (A + B) + δ_bch = BCH.suzuki5_bch ℝ A B p τ := by
    rw [hδ_bch_def]; abel
  -- Apply exp-Lipschitz: ‖exp(X + δ) - exp(X)‖ ≤ ‖δ‖ · exp(‖X‖ + ‖δ‖).
  have h_lip := BCH.norm_exp_add_sub_exp_le (𝕂 := ℝ) (τ • (A + B)) δ_bch
  rw [h_add] at h_lip
  -- Bound ‖δ_bch‖ = ‖suzuki5_bch - τ•(A+B)‖ ≤ τ⁵·Sfs + K·τ⁶.
  have hδ_bch_norm : ‖δ_bch‖ ≤ τ ^ 5 * Sfs + K * τ ^ 6 := h_log
  -- For τ ∈ [0, 1]: τ⁵·Sfs + K·τ⁶ ≤ (Sfs + K)·τ⁵ since τ⁶ ≤ τ⁵.
  have hτ5_nn : 0 ≤ τ ^ 5 := pow_nonneg hτ_nn 5
  have hτ6_le_τ5 : τ ^ 6 ≤ τ ^ 5 := by
    have : τ ^ 6 = τ * τ ^ 5 := by ring
    rw [this]
    calc τ * τ ^ 5 ≤ 1 * τ ^ 5 := by
            exact mul_le_mul_of_nonneg_right hτ_le_one hτ5_nn
      _ = τ ^ 5 := by ring
  have hδ_bch_poly : τ ^ 5 * Sfs + K * τ ^ 6 ≤ (Sfs + K) * τ ^ 5 := by
    have h1 : K * τ ^ 6 ≤ K * τ ^ 5 := mul_le_mul_of_nonneg_left hτ6_le_τ5 hK_nn
    nlinarith [hSfs_nn, hK_nn, hτ5_nn]
  have hδ_bch_le : ‖δ_bch‖ ≤ (Sfs + K) * τ ^ 5 := le_trans hδ_bch_norm hδ_bch_poly
  -- Bound ‖τ•(A+B)‖ ≤ τ · ‖A+B‖ ≤ ‖A+B‖ (since τ ≤ 1).
  have hτV_norm : ‖τ • (A + B)‖ ≤ ‖A + B‖ := by
    have h1 : ‖τ • (A + B)‖ ≤ ‖(τ : ℝ)‖ * ‖A + B‖ := norm_smul_le _ _
    have h2 : ‖(τ : ℝ)‖ = τ := by rw [Real.norm_eq_abs, abs_of_nonneg hτ_nn]
    rw [h2] at h1
    calc ‖τ • (A + B)‖ ≤ τ * ‖A + B‖ := h1
      _ ≤ 1 * ‖A + B‖ := mul_le_mul_of_nonneg_right hτ_le_one (norm_nonneg _)
      _ = ‖A + B‖ := by ring
  -- Bound the exp-Lipschitz factor.
  have h_exp_le : Real.exp (‖τ • (A + B)‖ + ‖δ_bch‖) ≤ Real.exp (‖A + B‖ + Sfs + K) := by
    apply Real.exp_le_exp.mpr
    have hδ_bch_le_SfsK : ‖δ_bch‖ ≤ Sfs + K := by
      calc ‖δ_bch‖ ≤ (Sfs + K) * τ ^ 5 := hδ_bch_le
        _ ≤ (Sfs + K) * 1 := by
            apply mul_le_mul_of_nonneg_left
            · calc τ ^ 5 ≤ 1 ^ 5 := pow_le_pow_left₀ hτ_nn hτ_le_one 5
                _ = 1 := one_pow 5
            · exact add_nonneg hSfs_nn hK_nn
        _ = Sfs + K := by ring
    linarith
  -- Now chain: ‖S₄ - exp(t•H)‖ ≤ ‖δ‖·exp(‖X‖+‖δ‖) ≤ (Sfs+K)·τ⁵·exp(‖A+B‖+Sfs+K) = C·τ⁵.
  have h_s4_eq : BCH.suzuki5Product (𝕂 := ℝ) A B p τ = suzuki4Exp A B p τ := by
    show BCH.suzuki5Product (𝕂 := ℝ) A B p τ = suzuki4Exp A B p τ
    rfl
  have h_lip' :
      ‖BCH.suzuki5Product (𝕂 := ℝ) A B p τ - exp (τ • (A + B))‖ ≤
        ‖δ_bch‖ * Real.exp (‖τ • (A + B)‖ + ‖δ_bch‖) := by
    rw [← h_exp_bch]; exact h_lip
  have h_final' :
      ‖BCH.suzuki5Product (𝕂 := ℝ) A B p τ - exp (τ • (A + B))‖ ≤ C * τ ^ 5 := by
    have hExp_factor_nn : 0 ≤ Real.exp (‖τ • (A + B)‖ + ‖δ_bch‖) := (Real.exp_pos _).le
    have hExp_target_nn : 0 ≤ Real.exp (‖A + B‖ + Sfs + K) := (Real.exp_pos _).le
    have hδ_bch_nn : 0 ≤ ‖δ_bch‖ := norm_nonneg _
    calc ‖BCH.suzuki5Product (𝕂 := ℝ) A B p τ - exp (τ • (A + B))‖
        ≤ ‖δ_bch‖ * Real.exp (‖τ • (A + B)‖ + ‖δ_bch‖) := h_lip'
      _ ≤ ((Sfs + K) * τ ^ 5) * Real.exp (‖A + B‖ + Sfs + K) := by
          apply mul_le_mul hδ_bch_le h_exp_le hExp_factor_nn
          exact mul_nonneg (add_nonneg hSfs_nn hK_nn) hτ5_nn
      _ = C * τ ^ 5 := by rw [hC_def]; ring
  rw [h_s4_eq] at h_final'
  exact h_final'

/-!
## Level 1 (Childs 2021 coefficient form): derived from Level 3

The theorem carrying Childs's coefficient vector
`{0.0047, 0.0057, 0.0046, 0.0074, 0.0097, 0.0097, 0.0173, 0.0284}` is
`norm_suzuki4_childs_explicit`, with the required `K'·τ⁶` remainder.
`norm_suzuki4_le_childs_near_zero` removes the remainder under a strict
leading-coefficient gap; `norm_suzuki4_childs_form_via_level3` is retained as
an order-only alias. These results use the Lean-proved termwise inequality
`γᵢ ≤ αᵢ` (`bchTightPrefactors_le_childs`).

**Axiom-elimination note (2026-04-23):** an earlier version of this file
carried a separate `bch_childs_pointwise_residual` axiom. That axiom was
retired: the coefficient statements now follow from the certified Level 3
bound and the proved comparison, while Childs et al.'s published proposition
remains a rigorous external reference whose coefficient optimality is open.
-/

/-!
## Level 3: Certified smaller leading prefactors via exact BCH expansion

Childs's rigorous-bound coefficients are `{0.0047, 0.0057, 0.0046, 0.0074,
0.0097, 0.0097, 0.0173, 0.0284}`; their tightness is not proved. Our exact
BCH quintic expansion and chosen projection give certified ceilings that are:
- Explicit rational functions of the Suzuki parameter `p`.
- Specialized at `p = 1/(4-4^(1/3))` to specific rational numbers.
- Strictly smaller than Childs's published values termwise.

### Framework

We encode the 8 BCH prefactors as an explicit `BCHPrefactors` structure,
define the certified rational ceilings, and derive the corresponding S₄
bound. The values of `bchTightPrefactors` are transcribed from a CAS-assisted
BCH expansion and verified through the inequalities used by the Lean proofs;
Lean-BCH supplies the formal algebraic bridge to the quintic residual.
-/

/-- Structure holding the 8 BCH prefactors, one per Childs 4-fold commutator. -/
structure BCHPrefactors where
  γ₁ : ℝ  -- coefficient of ‖[A,[A,[A,[B,A]]]]‖
  γ₂ : ℝ  -- coefficient of ‖[A,[A,[B,[B,A]]]]‖
  γ₃ : ℝ  -- coefficient of ‖[A,[B,[A,[B,A]]]]‖
  γ₄ : ℝ  -- coefficient of ‖[A,[B,[B,[B,A]]]]‖
  γ₅ : ℝ  -- coefficient of ‖[B,[A,[A,[B,A]]]]‖
  γ₆ : ℝ  -- coefficient of ‖[B,[A,[B,[B,A]]]]‖
  γ₇ : ℝ  -- coefficient of ‖[B,[B,[A,[B,A]]]]‖
  γ₈ : ℝ  -- coefficient of ‖[B,[B,[B,[B,A]]]]‖
  nonneg₁ : 0 ≤ γ₁ := by norm_num
  nonneg₂ : 0 ≤ γ₂ := by norm_num
  nonneg₃ : 0 ≤ γ₃ := by norm_num
  nonneg₄ : 0 ≤ γ₄ := by norm_num
  nonneg₅ : 0 ≤ γ₅ := by norm_num
  nonneg₆ : 0 ≤ γ₆ := by norm_num
  nonneg₇ : 0 ≤ γ₇ := by norm_num
  nonneg₈ : 0 ≤ γ₈ := by norm_num

/-- Coefficients in Childs et al. (2021)'s rigorous arXiv Proposition J.1
bound; the paper does not prove these coefficients tight. -/
def childsPrefactors : BCHPrefactors where
  γ₁ := 0.0047
  γ₂ := 0.0057
  γ₃ := 0.0046
  γ₄ := 0.0074
  γ₅ := 0.0097
  γ₆ := 0.0097
  γ₇ := 0.0173
  γ₈ := 0.0284
  nonneg₁ := by norm_num
  nonneg₂ := by norm_num
  nonneg₃ := by norm_num
  nonneg₄ := by norm_num
  nonneg₅ := by norm_num
  nonneg₆ := by norm_num
  nonneg₇ := by norm_num
  nonneg₈ := by norm_num

/-- **BCH-derived leading-order prefactors**, computed by
  `scripts/compute_bch_prefactors.py` via symbolic free-algebra BCH
  expansion of `log(S₄(τ)) - τ·(A+B)` to order τ⁵, then projection onto
  the Childs 8-commutator basis, then Suzuki cubic reduction.

  The symbolic expressions (polynomials of degree 2 in p, before
  specialization):
  ```
    γ₁(p) = 127p²/144000 + 13p/36000 − 1/24000
    γ₂(p) = p²/12000 + 13p/6000 − 1/4000
    γ₃(p) = 0
    γ₄(p) = −61p²/9000 + 13p/3000 − 1/2000
    γ₅(p) = 31p²/9000 − 13p/18000 + 1/12000
    γ₆(p) = 31p²/3000 − 13p/6000 + 1/4000
    γ₇(p) = 0
    γ₈(p) = p²/18000 + 13p/9000 − 1/6000
  ```
  At Suzuki `p = 1/(4 − 4^(1/3)) ≈ 0.4145`, the CAS-computed
  `|βᵢ(suzukiP)|` values are:
  ```
    |β₁| ≈ 0.0002595   |β₅| ≈ 0.0003757
    |β₂| ≈ 0.0006624   |β₆| ≈ 0.0011272
    |β₃| = 0           |β₇| = 0
    |β₄| ≈ 0.0001317   |β₈| ≈ 0.0004416
  ```
  We store **ceilings** at the 1/1000000 grid as the stored rational γᵢ
  values (e.g. γ₂ = 663/10⁶ > |β₂|), so `γᵢ ≥ |βᵢ(suzukiP)|` holds
  rigorously. This is essential for any provable R₅ norm bound
  `‖suzuki5_R5‖ ≤ boundSum` (prior versions used truncations which
  failed the bound by ~10⁻⁷ for γ₂ and γ₆).

  **Every ceiling value is strictly smaller than Childs's published
  coefficient** (8.6× to ~64× for non-zero values; two are
  exactly 0).

  Caveat: the Childs 8-commutator basis is **over-complete** (2 free
  parameters in the projection because the weight-5 free Lie algebra is
  6-dimensional). We chose the projection setting both free parameters
  to zero (which gives `γ₃ = γ₇ = 0`). Other valid projections may
  redistribute mass across the 8 coefficients. The stated domination is
  proved for this stored projection; arbitrary valid projections need not satisfy it.

  Note on correctness: these γᵢ bound the **leading-order** BCH
  quintic residual `R₅`. The full w4Deriv pointwise bound on `[0, t]`
  includes higher-order corrections which require the ambient convergence
  radius `t·(‖A‖+‖B‖) < 1/4` to be controlled. Childs's larger
  coefficients fold in these higher-order corrections; ours are pure
  leading-order. -/
def bchTightPrefactors : BCHPrefactors where
  γ₁ := 260 / 1000000    -- ceiling of |β₁(p*)| ≈ 0.0002595 (Childs: 0.0047, ~18× tighter)
  γ₂ := 663 / 1000000    -- ceiling of |β₂(p*)| ≈ 0.0006624 (Childs: 0.0057, ~8.6× tighter)
  γ₃ := 0                -- exactly 0 (Childs: 0.0046)
  γ₄ := 132 / 1000000    -- ceiling of |β₄(p*)| ≈ 0.0001317 (Childs: 0.0074, ~56× tighter)
  γ₅ := 376 / 1000000    -- ceiling of |β₅(p*)| ≈ 0.0003757 (Childs: 0.0097, ~26× tighter)
  γ₆ := 1128 / 1000000   -- ceiling of |β₆(p*)| ≈ 0.0011272 (Childs: 0.0097, ~8.6× tighter)
  γ₇ := 0                -- exactly 0 (Childs: 0.0173)
  γ₈ := 442 / 1000000    -- ceiling of |β₈(p*)| ≈ 0.0004416 (Childs: 0.0284, ~64× tighter)
  nonneg₁ := by norm_num
  nonneg₂ := by norm_num
  nonneg₃ := by norm_num
  nonneg₄ := by norm_num
  nonneg₅ := by norm_num
  nonneg₆ := by norm_num
  nonneg₇ := by norm_num
  nonneg₈ := by norm_num

/-- Weighted sum of Childs commutator norms with the given prefactors. -/
def BCHPrefactors.boundSum (γ : BCHPrefactors) (A B : 𝔸) : ℝ :=
  γ.γ₁ * ‖childsComm₁ A B‖ + γ.γ₂ * ‖childsComm₂ A B‖ +
  γ.γ₃ * ‖childsComm₃ A B‖ + γ.γ₄ * ‖childsComm₄ A B‖ +
  γ.γ₅ * ‖childsComm₅ A B‖ + γ.γ₆ * ‖childsComm₆ A B‖ +
  γ.γ₇ * ‖childsComm₇ A B‖ + γ.γ₈ * ‖childsComm₈ A B‖

omit [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] in
lemma BCHPrefactors.boundSum_nonneg (γ : BCHPrefactors) (A B : 𝔸) :
    0 ≤ γ.boundSum A B := by
  unfold BCHPrefactors.boundSum
  have := γ.nonneg₁; have := γ.nonneg₂; have := γ.nonneg₃; have := γ.nonneg₄
  have := γ.nonneg₅; have := γ.nonneg₆; have := γ.nonneg₇; have := γ.nonneg₈
  positivity

/-- `childsPrefactors.boundSum = childsBoundSum`. -/
lemma childsPrefactors_boundSum_eq (A B : 𝔸) :
    childsPrefactors.boundSum A B = childsBoundSum A B := by
  unfold BCHPrefactors.boundSum childsBoundSum childsPrefactors
  ring

omit [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] in
/-- **Key comparison**: the tight BCH prefactors produce a strictly smaller
  bound than Childs's (by construction, they are half of Childs's). -/
lemma bchTightPrefactors_le_childs (A B : 𝔸) :
    bchTightPrefactors.boundSum A B ≤ childsBoundSum A B := by
  unfold BCHPrefactors.boundSum bchTightPrefactors childsBoundSum
  have h₁ := norm_nonneg (childsComm₁ A B)
  have h₂ := norm_nonneg (childsComm₂ A B)
  have h₃ := norm_nonneg (childsComm₃ A B)
  have h₄ := norm_nonneg (childsComm₄ A B)
  have h₅ := norm_nonneg (childsComm₅ A B)
  have h₆ := norm_nonneg (childsComm₆ A B)
  have h₇ := norm_nonneg (childsComm₇ A B)
  have h₈ := norm_nonneg (childsComm₈ A B)
  nlinarith

section AntiHermitianLevel3

-- NOTE: the star-structure variables are already in scope from the enclosing
-- `AntiHermitian` section; re-declaring them here duplicated every instance
-- argument in the signatures below. The L1–L3 τ⁵ bounds do not use them at
-- all (they go through BCH + exp-Lipschitz, never the anti-Hermitian
-- isometry), so each is introduced with an explicit `omit`.

omit [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] in
/-- **Level 3 BCH τ⁵ identification with certified prefactors**. At Suzuki
  `p = 1/(4 − 4^(1/3))`, there exist `δ > 0` and `K ≥ 0` such that for
  all `τ ∈ [0, δ)`,
```
  ‖suzuki5_bch ℝ A B p τ − τ • (A + B)‖ ≤
    τ⁵ · bchTightPrefactors.boundSum A B + K · τ⁶
```
  where `bchTightPrefactors.γᵢ` are rational CEILINGS of `|βᵢ(suzukiP)|`
  at the 1/10⁶ grid (each strictly below the corresponding Childs
  coefficient; two are exactly 0).

  **Now a theorem (was an axiom).** Derived directly from Lean-BCH's
  tight bridge corollary
  `BCH.suzuki5_log_product_quintic_tight_at_suzukiP`. The Lean-BCH proof
  combines the headline τ⁵ identification with six rigorously-proved per-i
  numerical bounds `|βᵢ(suzukiP)| ≤ γᵢ` on the tight rational interval
  `41449/100000 < suzukiP < 41450/100000` via `nlinarith`.

  As of Lean-BCH pin `d455ff0` (2026-05-19), the upstream B1.c quintic
  axiom that previously gated this bridge has been discharged, so
  `#print axioms bch_w4Deriv_level3_tight` reports only the standard Lean
  foundational axioms `[propext, Classical.choice, Quot.sound]`. -/
theorem bch_w4Deriv_level3_tight (A B : 𝔸) :
    let p : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))
    ∃ δ > (0 : ℝ), ∃ K ≥ (0 : ℝ), ∀ τ : ℝ, 0 ≤ τ → τ < δ →
      ‖BCH.suzuki5_bch ℝ A B p τ - τ • (A + B)‖ ≤
        τ ^ 5 * bchTightPrefactors.boundSum A B + K * τ ^ 6 := by
  -- suzukiP (Lean-BCH) defeq-equal to p (Lean-Trotter).
  have h_bridge := BCH.suzuki5_log_product_quintic_tight_at_suzukiP A B
  -- Swap Lean-BCH's bchTightPrefactors.boundSum for Lean-Trotter's
  -- (same structure, same γ values — equal on the nose via unfold).
  have hbs_eq : BCH.bchTightPrefactors.boundSum A B =
      bchTightPrefactors.boundSum A B := by
    unfold BCH.BCHPrefactors.boundSum BCH.bchTightPrefactors
      BCHPrefactors.boundSum bchTightPrefactors
    rfl
  obtain ⟨δ, hδ_pos, K, hK_nn, h_bound⟩ := h_bridge
  refine ⟨δ, hδ_pos, K, hK_nn, ?_⟩
  intro τ hτ_nn hτ_lt
  have := h_bound τ hτ_nn hτ_lt
  -- Rewrite RHS using boundSum equality.
  rw [hbs_eq] at this
  exact this

omit [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] in
set_option maxHeartbeats 1000000 in
/-- **Exp-Lipschitz lift that preserves the leading coefficient.**

Every BCH bridge gives a τ⁵-identification of `log S₄(τ)` with an *explicit*
leading coefficient `S`:
```
  ‖suzuki5_bch τ − τ•(A+B)‖ ≤ τ⁵·S + K·τ⁶ .
```
Lifting this through `exp` is where the older `norm_suzuki4_level{2,3}_bch`
proofs threw the prefactor away, by (i) merging `τ⁵·S + K·τ⁶` into `(S+K)·τ⁵`
and (ii) multiplying through by `exp(‖A+B‖ + S + K)`.  Neither is necessary:
`exp u ≤ 1 + u·exp u` (from `1 − u ≤ exp(−u)`) makes the Lipschitz factor
`1 + O(τ)`, so its excess is absorbed into the τ⁶ remainder and `S` survives
*verbatim* as the leading coefficient.

This single lemma therefore upgrades every level of the hierarchy at once. -/
private lemma norm_suzuki4_sub_exp_le_of_log_bound
    (A B : 𝔸) (p : ℝ) {S K δ_log : ℝ} (hS : 0 ≤ S) (hK : 0 ≤ K) (hδ_log : 0 < δ_log)
    (hlog : ∀ τ : ℝ, 0 ≤ τ → τ < δ_log →
      ‖BCH.suzuki5_bch ℝ A B p τ - τ • (A + B)‖ ≤ τ ^ 5 * S + K * τ ^ 6) :
    ∃ δ > 0, ∃ K' ≥ 0, ∀ τ : ℝ, 0 ≤ τ → τ < δ →
      ‖suzuki4Exp A B p τ - exp (τ • (A + B))‖ ≤ τ ^ 5 * S + K' * τ ^ 6 := by
  have h_regime := exists_regime_nhds A B p
  rw [Metric.eventually_nhds_iff] at h_regime
  obtain ⟨δ_reg, hδ_reg_pos, h_regime⟩ := h_regime
  set δ := min δ_log (min δ_reg 1) with hδ_def
  have hδ_pos : 0 < δ := lt_min hδ_log (lt_min hδ_reg_pos one_pos)
  have hδ_le_log : δ ≤ δ_log := min_le_left _ _
  have hδ_le_reg : δ ≤ δ_reg := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ_le_one : δ ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hAB_nn : (0:ℝ) ≤ ‖A + B‖ := norm_nonneg _
  set M : ℝ := ‖A + B‖ + S + K with hM_def
  have hM_nn : 0 ≤ M := by rw [hM_def]; linarith
  have hE_pos : (0:ℝ) < Real.exp M := Real.exp_pos _
  have hSK_nn : (0:ℝ) ≤ S + K := by linarith
  have hKME_nn : (0:ℝ) ≤ K * M * Real.exp M :=
    mul_nonneg (mul_nonneg hK hM_nn) hE_pos.le
  refine ⟨δ, hδ_pos, K + (S + K) * M * Real.exp M, by
    have : (0:ℝ) ≤ (S + K) * M * Real.exp M :=
      mul_nonneg (mul_nonneg hSK_nn hM_nn) hE_pos.le
    linarith, ?_⟩
  intro τ hτ_nn hτ_lt
  have hτ_le_one : τ ≤ 1 := le_trans hτ_lt.le hδ_le_one
  have hτ_lt_log : τ < δ_log := lt_of_lt_of_le hτ_lt hδ_le_log
  have hτ_lt_reg : τ < δ_reg := lt_of_lt_of_le hτ_lt hδ_le_reg
  have hτ5_nn : (0:ℝ) ≤ τ ^ 5 := by positivity
  have hτ6_nn : (0:ℝ) ≤ τ ^ 6 := by positivity
  have hτ6_le_τ5 : τ ^ 6 ≤ τ ^ 5 := by
    have h6 : τ ^ 6 = τ * τ ^ 5 := by ring
    rw [h6]
    calc τ * τ ^ 5 ≤ 1 * τ ^ 5 := mul_le_mul_of_nonneg_right hτ_le_one hτ5_nn
      _ = τ ^ 5 := by ring
  have hτ7_le_τ6 : τ ^ 7 ≤ τ ^ 6 := by
    have h7 : τ ^ 7 = τ * τ ^ 6 := by ring
    rw [h7]
    calc τ * τ ^ 6 ≤ 1 * τ ^ 6 := mul_le_mul_of_nonneg_right hτ_le_one hτ6_nn
      _ = τ ^ 6 := by ring
  have hτ5_le_τ : τ ^ 5 ≤ τ := by
    have h5 : τ ^ 5 = τ * τ ^ 4 := by ring
    have h4 : τ ^ 4 ≤ 1 := pow_le_one₀ hτ_nn hτ_le_one
    rw [h5]
    calc τ * τ ^ 4 ≤ τ * 1 := mul_le_mul_of_nonneg_left h4 hτ_nn
      _ = τ := by ring
  have hτ_dist : dist τ 0 < δ_reg := by
    rw [Real.dist_eq]; simpa [abs_of_nonneg hτ_nn] using hτ_lt_reg
  obtain ⟨h_R, _, _, _, _, _⟩ := h_regime hτ_dist
  have h_log := hlog τ hτ_nn hτ_lt_log
  have h_exp_bch : exp (BCH.suzuki5_bch ℝ A B p τ) = BCH.suzuki5Product (𝕂 := ℝ) A B p τ :=
    BCH.exp_suzuki5_bch (𝕂 := ℝ) A B p τ h_R
  set d : 𝔸 := BCH.suzuki5_bch ℝ A B p τ - τ • (A + B) with hd_def
  have h_add : τ • (A + B) + d = BCH.suzuki5_bch ℝ A B p τ := by rw [hd_def]; abel
  have h_lip := BCH.norm_exp_add_sub_exp_le (𝕂 := ℝ) (τ • (A + B)) d
  rw [h_add] at h_lip
  have hd_norm : ‖d‖ ≤ τ ^ 5 * S + K * τ ^ 6 := h_log
  have hKτ6 : K * τ ^ 6 ≤ K * τ ^ 5 := mul_le_mul_of_nonneg_left hτ6_le_τ5 hK
  have hd_le_lin : ‖d‖ ≤ (S + K) * τ ^ 5 := by linarith [hd_norm, hKτ6]
  have hτV : ‖τ • (A + B)‖ ≤ τ * ‖A + B‖ := by
    have h1 : ‖τ • (A + B)‖ ≤ ‖(τ : ℝ)‖ * ‖A + B‖ := norm_smul_le _ _
    rwa [Real.norm_eq_abs, abs_of_nonneg hτ_nn] at h1
  have hu_le : ‖τ • (A + B)‖ + ‖d‖ ≤ τ * M := by
    have h5 : (S + K) * τ ^ 5 ≤ (S + K) * τ :=
      mul_le_mul_of_nonneg_left hτ5_le_τ hSK_nn
    have hexp : τ * M = τ * ‖A + B‖ + (S + K) * τ := by rw [hM_def]; ring
    rw [hexp]; linarith [hτV, hd_le_lin, h5]
  -- exp u ≤ 1 + u·exp u, hence the Lipschitz factor is 1 + O(τ).
  have h_exp_key : Real.exp (‖τ • (A + B)‖ + ‖d‖) ≤
      1 + (‖τ • (A + B)‖ + ‖d‖) * Real.exp (‖τ • (A + B)‖ + ‖d‖) := by
    have h := Real.add_one_le_exp (-(‖τ • (A + B)‖ + ‖d‖))
    rw [Real.exp_neg] at h
    have hpos : (0:ℝ) < Real.exp (‖τ • (A + B)‖ + ‖d‖) := Real.exp_pos _
    have h2 := mul_le_mul_of_nonneg_right h hpos.le
    rw [inv_mul_cancel₀ hpos.ne'] at h2
    nlinarith [h2]
  have hu_le_M : ‖τ • (A + B)‖ + ‖d‖ ≤ M := by
    refine le_trans hu_le ?_
    calc τ * M ≤ 1 * M := mul_le_mul_of_nonneg_right hτ_le_one hM_nn
      _ = M := by ring
  have h_exp_le : Real.exp (‖τ • (A + B)‖ + ‖d‖) ≤ 1 + τ * M * Real.exp M := by
    have hmul : (‖τ • (A + B)‖ + ‖d‖) * Real.exp (‖τ • (A + B)‖ + ‖d‖) ≤ (τ * M) * Real.exp M :=
      mul_le_mul hu_le (Real.exp_le_exp.mpr hu_le_M) (Real.exp_pos _).le
        (mul_nonneg hτ_nn hM_nn)
    nlinarith [h_exp_key, hmul]
  have h_lip' : ‖BCH.suzuki5Product (𝕂 := ℝ) A B p τ - exp (τ • (A + B))‖ ≤
      ‖d‖ * Real.exp (‖τ • (A + B)‖ + ‖d‖) := by
    rw [← h_exp_bch]; exact h_lip
  have hR_nn : (0:ℝ) ≤ τ ^ 5 * S + K * τ ^ 6 := by
    have h1 : (0:ℝ) ≤ τ ^ 5 * S := mul_nonneg hτ5_nn hS
    have h2 : (0:ℝ) ≤ K * τ ^ 6 := mul_nonneg hK hτ6_nn
    linarith
  have hmul : ‖d‖ * Real.exp (‖τ • (A + B)‖ + ‖d‖) ≤
      (τ ^ 5 * S + K * τ ^ 6) * (1 + τ * M * Real.exp M) :=
    mul_le_mul hd_norm h_exp_le (Real.exp_pos _).le hR_nn
  have hstep : (K * M * Real.exp M) * τ ^ 7 ≤ (K * M * Real.exp M) * τ ^ 6 :=
    mul_le_mul_of_nonneg_left hτ7_le_τ6 hKME_nn
  have hexpand : (τ ^ 5 * S + K * τ ^ 6) * (1 + τ * M * Real.exp M)
      = τ ^ 5 * S + K * τ ^ 6 + (S * M * Real.exp M) * τ ^ 6
        + (K * M * Real.exp M) * τ ^ 7 := by ring
  have hrhs : τ ^ 5 * S + (K + (S + K) * M * Real.exp M) * τ ^ 6
      = τ ^ 5 * S + K * τ ^ 6 + (S * M * Real.exp M) * τ ^ 6
        + (K * M * Real.exp M) * τ ^ 6 := by ring
  have h_final : ‖BCH.suzuki5Product (𝕂 := ℝ) A B p τ - exp (τ • (A + B))‖ ≤
      τ ^ 5 * S + (K + (S + K) * M * Real.exp M) * τ ^ 6 := by
    refine le_trans h_lip' (le_trans hmul ?_)
    rw [hexpand, hrhs]
    linarith [hstep]
  have h_s4_eq : BCH.suzuki5Product (𝕂 := ℝ) A B p τ = suzuki4Exp A B p τ := by rfl
  rw [h_s4_eq] at h_final
  exact h_final

omit [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] in
/-- **Level 2, sharp form**: the unit-coefficient four-fold commutator sum
  `Σᵢ ‖Cᵢ‖` is the leading coefficient *of the statement*.  Holds for every `p`
  satisfying the Suzuki cubic condition. -/
theorem norm_suzuki4_level2_explicit (A B : 𝔸) (p : ℝ) (hcubic : IsSuzukiCubic p) :
    ∃ δ > 0, ∃ K' ≥ 0, ∀ τ : ℝ, 0 ≤ τ → τ < δ →
      ‖suzuki4Exp A B p τ - exp (τ • (A + B))‖ ≤
        τ ^ 5 * bchFourFoldSum A B + K' * τ ^ 6 := by
  obtain ⟨δ_log, hδ_log_pos, K, hK_nn, hlog⟩ := bch_w4Deriv_quintic_level2 A B p hcubic
  have hFS : BCH.bchFourFoldSum A B = bchFourFoldSum A B := by
    unfold BCH.bchFourFoldSum bchFourFoldSum
    unfold childsComm₁ childsComm₂ childsComm₃ childsComm₄
      childsComm₅ childsComm₆ childsComm₇ childsComm₈ commBr
    rfl
  rw [hFS] at hlog
  exact norm_suzuki4_sub_exp_le_of_log_bound A B p (bchFourFoldSum_nonneg A B) hK_nn
    hδ_log_pos hlog

omit [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] in
/-- **Level 3, sharp form**: the certified γ-prefactor sum is the *leading
  coefficient of the statement*, not merely a witness chosen inside the proof.
  At Suzuki `p = 1/(4 − 4^(1/3))` there are `δ > 0` and `K' ≥ 0` with
```
  ‖S₄(τ) - exp(τ•H)‖ ≤ τ⁵ · Σᵢ γᵢ‖Cᵢ‖  +  K' · τ⁶       (0 ≤ τ < δ)
```
  This is the statement the manuscript advertises.  Contrast
  `norm_suzuki4_level3_bch` below, whose `∃ C, · ≤ C·τ⁵` shape records only the
  *order* τ⁵ and forgets every prefactor — it is implied by this one (and, at
  the level of propositions, also by `norm_suzuki4_level2_bch`). -/
theorem norm_suzuki4_level3_explicit (A B : 𝔸) :
    let p : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))
    ∃ δ > 0, ∃ K' ≥ 0, ∀ τ : ℝ, 0 ≤ τ → τ < δ →
      ‖suzuki4Exp A B p τ - exp (τ • (A + B))‖ ≤
        τ ^ 5 * bchTightPrefactors.boundSum A B + K' * τ ^ 6 := by
  obtain ⟨δ_log, hδ_log_pos, K, hK_nn, hlog⟩ := bch_w4Deriv_level3_tight A B
  exact norm_suzuki4_sub_exp_le_of_log_bound A B _
    (bchTightPrefactors.boundSum_nonneg A B) hK_nn hδ_log_pos hlog

omit [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] in
/-- **Childs 2021 bound, sharp form.** The leading coefficient is Childs's own
  `Σᵢ αᵢ‖Cᵢ‖`, obtained from `norm_suzuki4_level3_explicit` by the termwise
  inequality `γᵢ ≤ αᵢ` (`bchTightPrefactors_le_childs`).  This is a genuine
  reproduction of Childs et al.'s arXiv Proposition J.1 coefficient form: unlike
  `norm_suzuki4_childs_form_via_level3`, the Childs sum occurs *in the
  statement*. -/
theorem norm_suzuki4_childs_explicit (A B : 𝔸) :
    let p : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))
    ∃ δ > 0, ∃ K' ≥ 0, ∀ τ : ℝ, 0 ≤ τ → τ < δ →
      ‖suzuki4Exp A B p τ - exp (τ • (A + B))‖ ≤
        τ ^ 5 * childsBoundSum A B + K' * τ ^ 6 := by
  obtain ⟨δ, hδ, K', hK', h⟩ := norm_suzuki4_level3_explicit A B
  refine ⟨δ, hδ, K', hK', fun τ hτ0 hτδ => le_trans (h τ hτ0 hτδ) ?_⟩
  have := mul_le_mul_of_nonneg_left (bchTightPrefactors_le_childs A B) (pow_nonneg hτ0 5)
  linarith

omit [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] in
/-- **Level 3 BCH-derived order bound** (backward-compatible form):
  at Suzuki `p = 1/(4 − 4^(1/3))`, there exist `δ > 0` and `C ≥ 0` such
  that for all `τ ∈ [0, δ)`,
```
  ‖S₄(τ) - exp(τ•H)‖ ≤ C · τ⁵
```
  The theorem type records only the order `C·τ⁵`; use
  `norm_suzuki4_level3_explicit` for the certified γᵢ leading coefficient
  and the honest `K'·τ⁶` remainder. The γᵢ are strictly smaller termwise than
  the published Childs coefficients, but are not claimed globally optimal in
  the over-complete basis.

  Derivation: combine `bch_w4Deriv_level3_tight` (τ⁵ identification of
  `log S₄(τ)` with certified γᵢ) with the M2b round-trip
  `BCH.exp_suzuki5_bch` (`S₄(τ) = exp(suzuki5_bch τ)` in the
  small-coefficient regime) and exp-Lipschitz
  `BCH.norm_exp_add_sub_exp_le`. -/
theorem norm_suzuki4_level3_bch (A B : 𝔸) :
    let p : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))
    ∃ δ > 0, ∃ C ≥ 0, ∀ τ : ℝ, 0 ≤ τ → τ < δ →
      ‖suzuki4Exp A B p τ - exp (τ • (A + B))‖ ≤ C * τ ^ 5 := by
  -- Immediate from the sharp form: on `τ ≤ 1` the τ⁶ remainder is absorbed into
  -- the τ⁵ term.  (Retained for backward compatibility; the sharp form is the
  -- one that carries the mathematical content.)
  obtain ⟨δ, hδ_pos, K', hK'_nn, h⟩ := norm_suzuki4_level3_explicit A B
  have hSbs_nn : (0:ℝ) ≤ bchTightPrefactors.boundSum A B :=
    bchTightPrefactors.boundSum_nonneg A B
  refine ⟨min δ 1, lt_min hδ_pos one_pos,
    bchTightPrefactors.boundSum A B + K', by linarith, ?_⟩
  intro τ hτ_nn hτ_lt
  have hτ_lt_δ : τ < δ := lt_of_lt_of_le hτ_lt (min_le_left _ _)
  have hτ_le_one : τ ≤ 1 := le_of_lt (lt_of_lt_of_le hτ_lt (min_le_right _ _))
  have hτ5_nn : (0:ℝ) ≤ τ ^ 5 := by positivity
  have hτ6_le_τ5 : τ ^ 6 ≤ τ ^ 5 := by
    have h6 : τ ^ 6 = τ * τ ^ 5 := by ring
    rw [h6]
    calc τ * τ ^ 5 ≤ 1 * τ ^ 5 := mul_le_mul_of_nonneg_right hτ_le_one hτ5_nn
      _ = τ ^ 5 := by ring
  have hK'τ : K' * τ ^ 6 ≤ K' * τ ^ 5 := mul_le_mul_of_nonneg_left hτ6_le_τ5 hK'_nn
  calc ‖suzuki4Exp A B (1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))) τ - exp (τ • (A + B))‖
      ≤ τ ^ 5 * bchTightPrefactors.boundSum A B + K' * τ ^ 6 := h τ hτ_nn hτ_lt_δ
    _ ≤ (bchTightPrefactors.boundSum A B + K') * τ ^ 5 := by linarith

omit [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] in
/-- **Level 3 dominates Level 1 (Childs)** (pointwise): for any `τ ≥ 0`,
  `τ⁵·bchTightPrefactors.boundSum ≤ τ⁵·childsBoundSum`. -/
theorem norm_suzuki4_level3_le_childs_pointwise (A B : 𝔸)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    τ ^ 5 * bchTightPrefactors.boundSum A B ≤ τ ^ 5 * childsBoundSum A B := by
  apply mul_le_mul_of_nonneg_left (bchTightPrefactors_le_childs A B)
  positivity

omit [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] in
/-- **Childs-labelled order bound, derived from Level 3**:
  at Suzuki `p = 1/(4 − 4^(1/3))`, there exist `δ > 0` and `C ≥ 0` such
  that for all `τ ∈ [0, δ)`,
```
  ‖S₄(τ) - exp(τ•H)‖ ≤ C · τ⁵
```
  This backward-compatible theorem is definitionally the Level 3 order
  statement, so the Childs coefficients do not occur in its type. Use
  `norm_suzuki4_childs_explicit` for the published αᵢ coefficient plus the
  `K'·τ⁶` remainder, or `norm_suzuki4_le_childs_near_zero` for the no-remainder
  bound under a strict leading-coefficient gap. -/
theorem norm_suzuki4_childs_form_via_level3 (A B : 𝔸) :
    let p : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))
    ∃ δ > 0, ∃ C ≥ 0, ∀ τ : ℝ, 0 ≤ τ → τ < δ →
      ‖suzuki4Exp A B p τ - exp (τ • (A + B))‖ ≤ C * τ ^ 5 :=
  -- Level 3's existential bound already has the right shape;
  -- the Childs-dominance post-step is pointwise on τ^5 · boundSum.
  norm_suzuki4_level3_bch A B

/-!
## Level 4: local uniform bound (R₅ + R₇ CAS data)

The Level 3 bound `t⁵ · bchTightPrefactors.boundSum` has one remaining
caveat: it bounds the leading-order coefficient, not the uniform quantity
`sup_{t ∈ [0, t*]} ‖S₄(t) − e^{tH}‖ / t⁵`.

To produce a **uniform** BCH-derived bound, the script
`scripts/compute_bch_r7.py` extends the expansion to degree 7. It
verifies that degrees 2, 3, 4, 6 all vanish (palindromic + Suzuki for 3;
palindromic for 2, 4, 6), extracts the degree-7 residual `R₇`, and
bounds it crudely via the triangle inequality over the 126 seven-letter
words. At Suzuki `p`:
```
    K := Σ_{w : 7-letter word} |coef(w) at Suzuki p|  ≈  0.01951.
```
The bound `‖R₇(A, B)‖ ≤ K · max(‖A‖, ‖B‖)^7` follows from
`‖w‖ ≤ max(‖A‖,‖B‖)^7` for each 7-letter word.

The resulting **uniform bound**:
```
    ‖S₄(t) − e^{tH}‖  ≤  t⁵ · Σᵢ γᵢ‖Cᵢ‖  +  t⁷ · K · max(‖A‖, ‖B‖)^7
```
is rigorous for finite `t` and strictly tighter than Childs's
`t⁵ · Σᵢ αᵢ‖Cᵢ‖` whenever the R₇ correction `t² · K · max(‖A‖, ‖B‖)^7`
is smaller than the gap `Σᵢ (αᵢ - γᵢ)‖Cᵢ‖` — see the comparison lemma
below.
-/

/-- Upper bound on `K = Σ_w |coef(w)|` for the degree-7 residual R₇ of
  Suzuki S₄, computed by `scripts/compute_bch_r7.py` at Suzuki `p`.
  Precise CAS value: `K ≈ 0.019509`. We round up to `0.01951` for the
  Lean constant. -/
def bchR7UniformConstant : ℝ := 0.01951

lemma bchR7UniformConstant_nonneg : 0 ≤ bchR7UniformConstant := by
  unfold bchR7UniformConstant; norm_num

/-- Upper bound on `‖R₇(A, B)‖`: `K · max(‖A‖, ‖B‖)^7`, with `K` from CAS. -/
def bchR7Bound (A B : 𝔸) : ℝ :=
  bchR7UniformConstant * max ‖A‖ ‖B‖ ^ 7

/-!
### In-Lean numerical sanity checks for BCH prefactor values

These lemmas verify *within Lean* (without the CAS) that the numerical
values hard-coded in `bchTightPrefactors` and `bchR7UniformConstant` match
the reported CAS output with an explicit safety margin. They don't reach
  the BCH expansion theorem imported from Lean-BCH, but they close the manual
transcription gap "Python float → Lean literal".
-/

/-- `bchR7UniformConstant = 0.01951`: literal value, matches the CAS output
  `K ≈ 0.019509...` with an explicit round-up margin of ≈0.005%. -/
lemma bchR7UniformConstant_eq : bchR7UniformConstant = 0.01951 := rfl

/-- The chosen `bchR7UniformConstant = 0.01951` exceeds the exact CAS value
  `0.019509...` with a safety margin. Independently verifiable from the
  output of `scripts/compute_bch_r7.py`. -/
lemma bchR7UniformConstant_covers_cas : (0.019509 : ℝ) < bchR7UniformConstant := by
  unfold bchR7UniformConstant; norm_num

/-- A concrete upper bound on `bchR7UniformConstant`: `K < 1/50 = 0.02`.
  Useful for coarse downstream bounds that don't need the exact value. -/
lemma bchR7UniformConstant_lt : bchR7UniformConstant < (1 : ℝ) / 50 := by
  unfold bchR7UniformConstant; norm_num

/-- `bchTightPrefactors` all satisfy `γᵢ ≤ 0.00113` (the maximum across
  the 8 values is `γ₆ ≈ 0.001127`). -/
lemma bchTightPrefactors_le_uniform :
    bchTightPrefactors.γ₁ ≤ (113 : ℝ) / 100000 ∧
    bchTightPrefactors.γ₂ ≤ (113 : ℝ) / 100000 ∧
    bchTightPrefactors.γ₃ ≤ (113 : ℝ) / 100000 ∧
    bchTightPrefactors.γ₄ ≤ (113 : ℝ) / 100000 ∧
    bchTightPrefactors.γ₅ ≤ (113 : ℝ) / 100000 ∧
    bchTightPrefactors.γ₆ ≤ (113 : ℝ) / 100000 ∧
    bchTightPrefactors.γ₇ ≤ (113 : ℝ) / 100000 ∧
    bchTightPrefactors.γ₈ ≤ (113 : ℝ) / 100000 := by
  unfold bchTightPrefactors; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-- **Strict dominance margin** between Childs and our BCH prefactors:
  element-wise, `childs.γᵢ - bch.γᵢ ≥ 0.004` for every index except where
  both are tiny. Concretely, `α₈ - γ₈ = 0.0284 - 0.000442 = 0.027958`. -/
lemma childs_minus_bch_large_for_C8 :
    childsPrefactors.γ₈ - bchTightPrefactors.γ₈ > (279 : ℝ) / 10000 := by
  unfold childsPrefactors bchTightPrefactors; norm_num

lemma bchR7Bound_nonneg (A B : 𝔸) : 0 ≤ bchR7Bound A B := by
  unfold bchR7Bound
  have := bchR7UniformConstant_nonneg
  have hmax : 0 ≤ max ‖A‖ ‖B‖ := le_max_of_le_left (norm_nonneg A)
  positivity

/-- Bridge equation: Lean-BCH's `bchR7UniformConstant` equals Lean-Trotter's
(both are `0.01951`). -/
private lemma bchR7UniformConstant_eq_BCH :
    BCH.bchR7UniformConstant = bchR7UniformConstant := by
  rw [BCH.bchR7UniformConstant_eq, bchR7UniformConstant_eq]

/-- Bridge equation: Lean-BCH's `bchR7Bound` equals Lean-Trotter's.
Both unfold to `0.01951 * max ‖A‖ ‖B‖^7`. -/
private lemma bchR7Bound_eq_BCH (A B : 𝔸) :
    BCH.bchR7Bound A B = bchR7Bound A B := by
  unfold BCH.bchR7Bound bchR7Bound
  rw [bchR7UniformConstant_eq_BCH]

/-- **Level 4 uniform BCH Trotter bound** (existential-δ form): finite-`t`
  bound combining the leading R₅ prefactors with an explicit R₇ correction.

  At Suzuki `p = 1/(4 − 4^(1/3))`, there exist `δ > 0` and `C ≥ 0` such that
  for all `τ ∈ [0, δ)`,
```
  ‖S₄(τ) − e^{τH}‖ ≤
    C · (τ⁵ · bchTightPrefactors.boundSum A B +
         τ⁷ · bchR7Bound A B +
         τ⁸)
```

  Compared to Level 3's coarser `C · τ⁵` shape, this preserves the explicit
  `τ⁵·boundSum` and `τ⁷·R7Bound` separation: the leading-order content of
  the R₅ residual sits in the `τ⁵·boundSum` term, the next-order R₇
  correction sits in the `τ⁷·R7Bound` term, and `C·τ⁸` absorbs the
  exp-Lipschitz inflation factor and the BCH `O(τ⁸)` tail.

  **Now a theorem (was an axiom).** Derived from Lean-BCH's bridge corollary
  `BCH.suzuki5_log_product_septic_at_suzukiP`. At Lean-BCH revision
  `05e8c52` (2026-07-28), both former septic stepping stones are proved, so
  this complete τ⁷ chain and the L4 uniform refinement have no
  project-specific axiom dependency. -/
theorem bch_uniform_integrated
    (A B : 𝔸) (hA : star A = -A) (hB : star B = -B) :
    let p : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))
    ∃ δ > 0, ∃ C ≥ 0, ∀ τ : ℝ, 0 ≤ τ → τ < δ →
      ‖suzuki4Exp A B p τ - exp (τ • (A + B))‖ ≤
        C * (τ ^ 5 * bchTightPrefactors.boundSum A B +
             τ ^ 7 * bchR7Bound A B +
             τ ^ 8) := by
  set p : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3)) with hp_def
  -- Cubic hypothesis is automatically satisfied by p's definition.
  have hcubic : BCH.IsSuzukiCubic p := by
    rw [hp_def]; exact BCH.IsSuzukiCubic_suzukiP
  -- Step 1: get the BCH septic identification (τ⁵ R₅ + τ⁷ R₇ + M·τ⁸ tail).
  obtain ⟨δ_log, hδ_log_pos, M_BCH, hM_BCH_nn, h_log_bound⟩ :=
    BCH.suzuki5_log_product_septic_at_suzukiP A B
  -- Step 2: small-coefficient regime for the M2b round-trip.
  have h_regime := exists_regime_nhds A B p
  rw [Metric.eventually_nhds_iff] at h_regime
  obtain ⟨δ_reg, hδ_reg_pos, h_regime⟩ := h_regime
  -- Step 3: shrink δ to ensure τ ≤ 1 (so the polynomial bookkeeping is uniform).
  set δ := min δ_log (min δ_reg 1) with hδ_def
  have hδ_pos : 0 < δ := lt_min hδ_log_pos (lt_min hδ_reg_pos (by norm_num : (0:ℝ) < 1))
  have hδ_le_log : δ ≤ δ_log := min_le_left _ _
  have hδ_le_reg : δ ≤ δ_reg := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ_le_one : δ ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
  -- Step 4: define the explicit constant C absorbing the exp-Lipschitz factor.
  set Sbs := bchTightPrefactors.boundSum A B with hSbs_def
  have hSbs_nn : 0 ≤ Sbs := bchTightPrefactors.boundSum_nonneg A B
  set R7B := bchR7Bound A B with hR7B_def
  have hR7B_nn : 0 ≤ R7B := bchR7Bound_nonneg A B
  set V_norm := ‖A + B‖ with hV_def
  have hV_nn : 0 ≤ V_norm := norm_nonneg _
  -- D bounds ‖τV‖ + ‖δ_bch‖ for τ ≤ 1.
  set D := V_norm + Sbs + R7B + M_BCH with hD_def
  have hD_nn : 0 ≤ D := by
    rw [hD_def]; positivity
  set E := Real.exp D with hE_def
  have hE_pos : 0 < E := Real.exp_pos _
  have hE_ge_one : 1 ≤ E := by
    rw [hE_def]; exact Real.one_le_exp hD_nn
  -- C := E·(1 + M_BCH) absorbs both the exp factor and the BCH tail constant.
  set C := E * (1 + M_BCH) with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    refine mul_nonneg hE_pos.le ?_
    linarith
  refine ⟨δ, hδ_pos, C, hC_nn, ?_⟩
  intro τ hτ_nn hτ_lt
  -- Pointwise regime + log bound at this τ.
  have hτ_lt_log : τ < δ_log := lt_of_lt_of_le hτ_lt hδ_le_log
  have hτ_lt_reg : τ < δ_reg := lt_of_lt_of_le hτ_lt hδ_le_reg
  have hτ_le_one : τ ≤ 1 := le_trans hτ_lt.le hδ_le_one
  have hτ_dist : dist τ 0 < δ_reg := by
    rw [Real.dist_eq]; simpa [abs_of_nonneg hτ_nn] using hτ_lt_reg
  obtain ⟨h_R, _h_pτ, _h_1m4pτ, _h_regsb, _h_Zbch, _h_nested⟩ := h_regime hτ_dist
  have h_log := h_log_bound τ hτ_nn hτ_lt_log
  -- Convert Lean-BCH's bchR7Bound to Lean-Trotter's bchR7Bound.
  rw [bchR7Bound_eq_BCH A B] at h_log
  -- M2b round-trip: S₄(τ) = exp(suzuki5_bch τ).
  have h_exp_bch : exp (BCH.suzuki5_bch ℝ A B p τ) = BCH.suzuki5Product (𝕂 := ℝ) A B p τ :=
    BCH.exp_suzuki5_bch (𝕂 := ℝ) A B p τ h_R
  set δ_bch := BCH.suzuki5_bch ℝ A B p τ - τ • (A + B) with hδ_bch_def
  have h_add : τ • (A + B) + δ_bch = BCH.suzuki5_bch ℝ A B p τ := by
    rw [hδ_bch_def]; abel
  -- Apply exp-Lipschitz: ‖exp(X+δ) - exp(X)‖ ≤ ‖δ‖·exp(‖X‖+‖δ‖).
  have h_lip := BCH.norm_exp_add_sub_exp_le (𝕂 := ℝ) (τ • (A + B)) δ_bch
  -- Bound ‖δ_bch‖ from BCH septic identification.
  have hδ_bch_norm : ‖δ_bch‖ ≤ τ ^ 5 * Sbs + τ ^ 7 * R7B + M_BCH * τ ^ 8 := h_log
  -- Simple positivity facts.
  have hτ5_nn : 0 ≤ τ ^ 5 := pow_nonneg hτ_nn 5
  have hτ7_nn : 0 ≤ τ ^ 7 := pow_nonneg hτ_nn 7
  have hτ8_nn : 0 ≤ τ ^ 8 := pow_nonneg hτ_nn 8
  -- For τ ∈ [0, 1]: τ⁵, τ⁷, τ⁸ ≤ 1.
  have hτ5_le_one : τ ^ 5 ≤ 1 := by
    calc τ ^ 5 ≤ 1 ^ 5 := pow_le_pow_left₀ hτ_nn hτ_le_one 5
      _ = 1 := one_pow _
  have hτ7_le_one : τ ^ 7 ≤ 1 := by
    calc τ ^ 7 ≤ 1 ^ 7 := pow_le_pow_left₀ hτ_nn hτ_le_one 7
      _ = 1 := one_pow _
  have hτ8_le_one : τ ^ 8 ≤ 1 := by
    calc τ ^ 8 ≤ 1 ^ 8 := pow_le_pow_left₀ hτ_nn hτ_le_one 8
      _ = 1 := one_pow _
  -- ‖δ_bch‖ ≤ Sbs + R7B + M_BCH (from the bound + τ^k ≤ 1).
  have hδ_bch_le_const : ‖δ_bch‖ ≤ Sbs + R7B + M_BCH := by
    calc ‖δ_bch‖ ≤ τ ^ 5 * Sbs + τ ^ 7 * R7B + M_BCH * τ ^ 8 := hδ_bch_norm
      _ ≤ 1 * Sbs + 1 * R7B + M_BCH * 1 := by gcongr
      _ = Sbs + R7B + M_BCH := by ring
  -- ‖τV‖ ≤ τ·V_norm ≤ V_norm.
  have hτV_norm_le : ‖τ • (A + B)‖ ≤ V_norm := by
    rw [hV_def]
    have h1 : ‖τ • (A + B)‖ ≤ ‖(τ : ℝ)‖ * ‖A + B‖ := norm_smul_le _ _
    have h2 : ‖(τ : ℝ)‖ = τ := by rw [Real.norm_eq_abs, abs_of_nonneg hτ_nn]
    rw [h2] at h1
    calc ‖τ • (A + B)‖ ≤ τ * ‖A + B‖ := h1
      _ ≤ 1 * ‖A + B‖ := mul_le_mul_of_nonneg_right hτ_le_one (norm_nonneg _)
      _ = ‖A + B‖ := one_mul _
  -- exp(‖τV‖ + ‖δ_bch‖) ≤ exp(D) = E.
  have h_exp_le : Real.exp (‖τ • (A + B)‖ + ‖δ_bch‖) ≤ E := by
    rw [hE_def]
    apply Real.exp_le_exp.mpr
    rw [hD_def]
    linarith [hτV_norm_le, hδ_bch_le_const]
  -- The big estimate, all in one go.
  have hδ_bch_nn : 0 ≤ ‖δ_bch‖ := norm_nonneg _
  -- Step A: ‖exp(τV+δ_bch) - exp(τV)‖ ≤ ‖δ_bch‖ · E
  have h_lip_E : ‖exp (τ • (A + B) + δ_bch) - exp (τ • (A + B))‖ ≤ ‖δ_bch‖ * E :=
    le_trans h_lip (mul_le_mul_of_nonneg_left h_exp_le hδ_bch_nn)
  -- Step B: rewrite LHS via M2b round-trip.
  rw [h_add] at h_lip_E
  rw [h_exp_bch] at h_lip_E
  -- Now: ‖suzuki5Product - exp(τV)‖ ≤ ‖δ_bch‖ · E.
  have h_s4_eq : BCH.suzuki5Product (𝕂 := ℝ) A B p τ = suzuki4Exp A B p τ := rfl
  rw [h_s4_eq] at h_lip_E
  -- Step C: ‖δ_bch‖ · E ≤ E · (τ⁵·Sbs + τ⁷·R7B + M_BCH·τ⁸).
  have h_prod : ‖δ_bch‖ * E ≤ E * (τ ^ 5 * Sbs + τ ^ 7 * R7B + M_BCH * τ ^ 8) := by
    rw [mul_comm ‖δ_bch‖ E]
    exact mul_le_mul_of_nonneg_left hδ_bch_norm hE_pos.le
  -- Step D: E · (τ⁵·Sbs + τ⁷·R7B + M_BCH·τ⁸) ≤ C · (τ⁵·Sbs + τ⁷·R7B + τ⁸).
  -- Since C = E · (1 + M_BCH), we have C ≥ E ≥ E·M_BCH (when M_BCH ≤ 1+M_BCH).
  have h_target :
      E * (τ ^ 5 * Sbs + τ ^ 7 * R7B + M_BCH * τ ^ 8) ≤
        C * (τ ^ 5 * Sbs + τ ^ 7 * R7B + τ ^ 8) := by
    have hC_ge_E : E ≤ C := by
      rw [hC_def]
      calc E = E * 1 := (mul_one E).symm
        _ ≤ E * (1 + M_BCH) := by
            apply mul_le_mul_of_nonneg_left _ hE_pos.le
            linarith
    have hC_ge_E_M : E * M_BCH ≤ C := by
      rw [hC_def]
      apply mul_le_mul_of_nonneg_left _ hE_pos.le
      linarith
    have ha : E * (τ ^ 5 * Sbs) ≤ C * (τ ^ 5 * Sbs) :=
      mul_le_mul_of_nonneg_right hC_ge_E (by positivity)
    have hb : E * (τ ^ 7 * R7B) ≤ C * (τ ^ 7 * R7B) :=
      mul_le_mul_of_nonneg_right hC_ge_E (by positivity)
    have hc : E * (M_BCH * τ ^ 8) ≤ C * τ ^ 8 := by
      calc E * (M_BCH * τ ^ 8) = (E * M_BCH) * τ ^ 8 := by ring
        _ ≤ C * τ ^ 8 := mul_le_mul_of_nonneg_right hC_ge_E_M hτ8_nn
    linarith
  -- Combine A, C, D.
  linarith [h_lip_E, h_prod, h_target]

/-- **Level 4 uniform BCH Trotter bound** (existential-δ form, exposed
under the original name for backward compatibility): same statement as
`bch_uniform_integrated`, just renamed. -/
theorem norm_suzuki4_level4_uniform (A B : 𝔸)
    (hA : star A = -A) (hB : star B = -B) :
    let p : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))
    ∃ δ > 0, ∃ C ≥ 0, ∀ τ : ℝ, 0 ≤ τ → τ < δ →
      ‖suzuki4Exp A B p τ - exp (τ • (A + B))‖ ≤
        C * (τ ^ 5 * bchTightPrefactors.boundSum A B +
             τ ^ 7 * bchR7Bound A B +
             τ ^ 8) :=
  bch_uniform_integrated A B hA hB

omit [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] in
/-- **The BCH bound dominates Childs's near zero.**

  Whenever the two leading coefficients differ strictly — i.e. some commutator
  with a strictly-smaller BCH prefactor is nonzero — the BCH-derived bound beats
  Childs's *on an existential neighbourhood of `0`*, with Childs's own coefficient
  and **no** remainder term:
```
  ‖S₄(τ) − e^{τH}‖ ≤ τ⁵ · Σᵢ αᵢ‖Cᵢ‖        (0 ≤ τ < δ)
```
  Derived from the sharp `norm_suzuki4_level3_explicit`: the τ⁶ remainder `K'·τ⁶`
  is `τ⁵·(K'τ)`, and `K'τ` is below the gap `Σ(αᵢ−γᵢ)‖Cᵢ‖` once `τ < gap/(K'+1)`.

  **This replaces `norm_suzuki4_level4_le_childs_when_small`**, which was vacuous:
  its side condition constrained an *existentially bound* `C`, so a prover could
  return a `C` large enough to falsify the hypothesis and discharge the
  implication empty.  (That theorem was provable with no BCH content at all.)
  The present statement has no such escape hatch — and, routing through Level 3
  rather than Level 4, it needs neither anti-Hermiticity nor a C*-algebra. -/
theorem norm_suzuki4_le_childs_near_zero (A B : 𝔸)
    (hgap : bchTightPrefactors.boundSum A B < childsBoundSum A B) :
    let p : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))
    ∃ δ > 0, ∀ τ : ℝ, 0 ≤ τ → τ < δ →
      ‖suzuki4Exp A B p τ - exp (τ • (A + B))‖ ≤ τ ^ 5 * childsBoundSum A B := by
  obtain ⟨δ₀, hδ₀_pos, K', hK'_nn, hstep⟩ := norm_suzuki4_level3_explicit A B
  set Sbs := bchTightPrefactors.boundSum A B with hSbs_def
  set cbs := childsBoundSum A B with hcbs_def
  set gap : ℝ := cbs - Sbs with hgap_def
  have hgap_pos : 0 < gap := by rw [hgap_def]; linarith
  have hK1_pos : (0 : ℝ) < K' + 1 := by linarith
  refine ⟨min δ₀ (gap / (K' + 1)), lt_min hδ₀_pos (by positivity), ?_⟩
  intro τ hτ_nn hτ_lt
  have hτ_lt_δ₀ : τ < δ₀ := lt_of_lt_of_le hτ_lt (min_le_left _ _)
  have hτ_lt_gap : τ < gap / (K' + 1) := lt_of_lt_of_le hτ_lt (min_le_right _ _)
  have hτ5_nn : (0 : ℝ) ≤ τ ^ 5 := by positivity
  -- The τ⁶ remainder stays below the α−γ gap.
  have hK'τ : K' * τ ≤ gap := by
    have h1 : τ * (K' + 1) < gap := by
      rw [lt_div_iff₀ hK1_pos] at hτ_lt_gap; linarith
    nlinarith [hτ_nn, hK'_nn]
  calc ‖suzuki4Exp A B (1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))) τ - exp (τ • (A + B))‖
      ≤ τ ^ 5 * Sbs + K' * τ ^ 6 := hstep τ hτ_nn hτ_lt_δ₀
    _ = τ ^ 5 * (Sbs + K' * τ) := by ring
    _ ≤ τ ^ 5 * (Sbs + gap) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hτ5_nn
    _ = τ ^ 5 * cbs := by rw [hgap_def]; ring

end AntiHermitianLevel3

end AntiHermitian

end
