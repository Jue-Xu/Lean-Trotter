/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Taylor Match from Norm Bound

General-purpose reverse direction of Taylor's theorem: if two `ContDiff ℝ k`
functions `f, g : ℝ → 𝔸` agree to order `k+1` near `0` (i.e. their difference
is bounded pointwise by `C · |τ|^{k+1}` on a neighbourhood of `0`), then their
iterated derivatives at `0` match for all orders `j ≤ k`.

Equivalently: if a `ContDiff ℝ k` function `h : ℝ → 𝔸` satisfies
`‖h τ‖ ≤ C · |τ|^{k+1}` near `0`, then `iteratedDeriv j h 0 = 0` for all
`j ≤ k`.

## Strategy

1. Let `h := f - g`. Then `h` is `ContDiff ℝ k` and bounded by `C·|τ|^{k+1}`
   near `0`, so in little-o terms `h =o[𝓝 0] (fun τ => τ^k)`.
2. By Mathlib's `taylor_isLittleO_univ`,
   `h τ - taylorWithinEval h k univ 0 τ =o[𝓝 0] (fun τ => τ^k)`.
3. Subtract: `taylorWithinEval h k univ 0 τ =o[𝓝 0] (fun τ => τ^k)`.
4. `taylorWithinEval h k univ 0 τ = Σⱼ ∈ range (k+1), (j!)⁻¹ • τ^j • iteratedDeriv j h 0`.
5. **Polynomial uniqueness at 0**: a polynomial `Σⱼ ≤ k, τ^j • aⱼ` that is
   `o(τ^k)` at `𝓝 0` must have all `aⱼ = 0`.
6. Conclude `iteratedDeriv j h 0 = 0` for all `j ≤ k`, hence
   `iteratedDeriv j f 0 = iteratedDeriv j g 0`.

## Main results

- `sum_smul_pow_eq_zero_of_isLittleO`: polynomial uniqueness at `0`.
- `iteratedDeriv_eq_zero_of_norm_le_pow`: vanishing from norm bound (corollary).
- `iteratedDeriv_eq_of_norm_le_pow`: Taylor-match lemma (main).
-/

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section

open Asymptotics Set Filter
open scoped Topology

/-! ### Helper: polynomial uniqueness at `0` -/

/-- Helper: the polynomial `fun τ => ∑ⱼ, τ^j • aⱼ` is continuous on `ℝ`. -/
private lemma continuous_sum_smul_pow
    {𝔸 : Type*} [NormedAddCommGroup 𝔸] [NormedSpace ℝ 𝔸]
    (n : ℕ) (a : ℕ → 𝔸) :
    Continuous (fun τ : ℝ => ∑ j ∈ Finset.range (n + 1), τ ^ j • a j) :=
  continuous_finset_sum _ fun j _ => (continuous_pow j).smul continuous_const

/-- Helper: If `f` is continuous at `0` and `f =o[𝓝[≠] 0] (fun τ => τ^k)`,
  then `f =o[𝓝 0] (fun τ => τ^k)`.

  The argument: continuity forces `f 0 = 0` (limit of values bounded by
  `‖τ^k‖ → 0` when `k ≥ 1`; or by `ε` for all `ε` when `k = 0`). Once
  `f 0 = 0`, the bound trivially holds at `τ = 0`, so it extends from
  the punctured neighbourhood to the full one. -/
lemma isLittleO_of_nhdsNE_of_continuousAt
    {𝔸 : Type*} [NormedAddCommGroup 𝔸]
    {f : ℝ → 𝔸} {k : ℕ}
    (hf_cont : ContinuousAt f 0)
    (hf : f =o[𝓝[≠] (0 : ℝ)] fun τ : ℝ => τ ^ k) :
    f =o[𝓝 (0 : ℝ)] fun τ : ℝ => τ ^ k := by
  -- First, `f 0 = 0` by continuity and the fact that the bound goes to 0.
  have h_tend_f : Tendsto f (𝓝 (0 : ℝ)) (𝓝 (f 0)) := hf_cont
  have h_tend_f_ne : Tendsto f (𝓝[≠] (0 : ℝ)) (𝓝 (f 0)) :=
    h_tend_f.mono_left nhdsWithin_le_nhds
  have h_norm_tend : Tendsto (fun τ => ‖f τ‖) (𝓝[≠] (0 : ℝ)) (𝓝 ‖f 0‖) :=
    h_tend_f_ne.norm
  have hf0 : f 0 = 0 := by
    rw [← norm_eq_zero]
    -- Pick ε = ‖f 0‖ + 1 > 0 if ‖f 0‖ > 0 leads to a bound ε * ‖τ^k‖ that
    -- must exceed the limit ‖f 0‖; use ε = ‖f 0‖/2 for contradiction.
    by_contra h_ne
    have h_pos : 0 < ‖f 0‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h_ne)
    -- Use ε = ‖f 0‖ / (1 + ‖(0 : ℝ)^k‖) to get a contradiction for both k=0 and k≥1.
    -- Simpler: use k=0 vs k≥1 case split.
    by_cases hk : k = 0
    · subst hk
      -- Bound: ‖f τ‖ ≤ ε on punctured; take ε = ‖f 0‖ / 2.
      have hε : 0 < ‖f 0‖ / 2 := by linarith
      have h_bnd := hf.def hε
      have h_bnd' : ∀ᶠ τ : ℝ in 𝓝[≠] 0, ‖f τ‖ ≤ ‖f 0‖ / 2 := by
        filter_upwards [h_bnd] with τ hτ
        simpa using hτ
      have h_le := le_of_tendsto h_norm_tend h_bnd'
      linarith
    · -- k ≥ 1: τ^k → 0 as τ → 0 on punctured.
      have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
      have h_pow_tend : Tendsto (fun τ : ℝ => (τ : ℝ) ^ k) (𝓝 (0 : ℝ)) (𝓝 0) := by
        have : Tendsto (fun τ : ℝ => τ) (𝓝 (0 : ℝ)) (𝓝 0) := tendsto_id
        have hp := this.pow k
        rwa [zero_pow hk] at hp
      have h_pow_tend_ne : Tendsto (fun τ : ℝ => ‖τ ^ k‖) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
        have : Tendsto (fun τ : ℝ => τ ^ k) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
          h_pow_tend.mono_left nhdsWithin_le_nhds
        simpa using this.norm
      have h_bound_1 := hf.def one_pos
      have h_bnd' : ∀ᶠ τ : ℝ in 𝓝[≠] 0, ‖f τ‖ ≤ ‖τ ^ k‖ := by
        filter_upwards [h_bound_1] with τ hτ; simpa using hτ
      have : ‖f 0‖ ≤ 0 := le_of_tendsto_of_tendsto h_norm_tend h_pow_tend_ne h_bnd'
      linarith
  -- Now extend `hf : f =o[𝓝[≠] 0] τ^k` to `𝓝 0` using `f 0 = 0`.
  rw [isLittleO_iff]
  intro ε hε
  have h_bnd := hf.def hε
  -- `h_bnd : ∀ᶠ τ in 𝓝[≠] 0, ‖f τ‖ ≤ ε · ‖τ^k‖`
  -- Rewrite: `∀ᶠ τ in 𝓝 0, τ ≠ 0 → ‖f τ‖ ≤ ε · ‖τ^k‖`.
  rw [eventually_nhdsWithin_iff] at h_bnd
  -- Goal: `∀ᶠ τ in 𝓝 0, ‖f τ‖ ≤ ε · ‖τ^k‖`
  -- Strategy: case-split on τ = 0 within the eventually-bound.
  filter_upwards [h_bnd] with τ hτ
  by_cases h : τ = 0
  · subst h
    rw [hf0]; simp; positivity
  · exact hτ h

/-- **Polynomial uniqueness (at `0`, order-`n`)**: if a polynomial
`P(τ) = Σⱼ ∈ range (n+1), τ^j • aⱼ` is `o(τ^n)` as `τ → 0`, then all
coefficients `aⱼ` vanish for `j ≤ n`.

Proof: induction on `n`.

- **Base `n = 0`:** the sum is `a 0`, hypothesis becomes `(fun _ => a 0) =o[𝓝 0] 1`,
  equivalently `Tendsto (fun _ => a 0) (𝓝 0) (𝓝 0)`, forcing `a 0 = 0`.
- **Step `n ↦ n+1`:**
  - Show `a 0 = 0` via `IsBigO.eq_zero_of_norm_pow` applied to `P =O[𝓝 0] τ^{n+1}`.
  - With `a 0 = 0`, factor `τ` out: `P τ = τ • Q τ` where `Q τ = Σⱼ τ^j • a(j+1)`.
  - On the punctured neighbourhood, `Q =o[𝓝[≠] 0] τ^n` (cancel `τ` using `‖τ‖ > 0`).
  - Since `Q` is continuous, extend `Q =o[𝓝 0] τ^n` via `of_nhdsNE_of_continuousAt`.
  - Apply IH to `Q`.
-/
lemma sum_smul_pow_eq_zero_of_isLittleO
    {𝔸 : Type*} [NormedAddCommGroup 𝔸] [NormedSpace ℝ 𝔸]
    {n : ℕ} (a : ℕ → 𝔸)
    (h : (fun τ : ℝ => ∑ j ∈ Finset.range (n + 1), τ ^ j • a j) =o[𝓝 0]
          fun τ : ℝ => τ ^ n) :
    ∀ j ≤ n, a j = 0 := by
  induction n generalizing a with
  | zero =>
    have hsum : (fun τ : ℝ => ∑ j ∈ Finset.range (0 + 1), τ ^ j • a j) = fun _ => a 0 := by
      funext τ; simp
    have hpow : (fun τ : ℝ => τ ^ 0) = fun _ : ℝ => (1 : ℝ) := by
      funext τ; simp
    rw [hsum, hpow] at h
    have htend : Tendsto (fun _ : ℝ => a 0) (𝓝 (0 : ℝ)) (𝓝 (0 : 𝔸)) :=
      (isLittleO_one_iff ℝ).mp h
    have hconst : Tendsto (fun _ : ℝ => a 0) (𝓝 (0 : ℝ)) (𝓝 (a 0)) := tendsto_const_nhds
    have ha0 : a 0 = 0 := tendsto_nhds_unique hconst htend
    intro j hj
    have : j = 0 := Nat.le_zero.mp hj
    subst this
    exact ha0
  | succ m ih =>
    -- Step A: `a 0 = 0` via `IsBigO.eq_zero_of_norm_pow`.
    have hBigO : (fun τ : ℝ => ∑ j ∈ Finset.range (m + 1 + 1), τ ^ j • a j) =O[𝓝 0]
                   fun τ : ℝ => ‖τ - (0 : ℝ)‖ ^ (m + 1) := by
      have h1 := h.isBigO
      have h2 : (fun τ : ℝ => τ ^ (m + 1)) =O[𝓝 0] fun τ : ℝ => ‖τ - (0 : ℝ)‖ ^ (m + 1) := by
        refine IsBigO.of_bound 1 ?_
        filter_upwards with τ
        rw [sub_zero, one_mul]
        -- Goal: ‖τ^(m+1)‖ ≤ ‖‖τ‖^(m+1)‖
        have e1 : ‖τ ^ (m + 1)‖ = ‖τ‖ ^ (m + 1) := norm_pow τ (m + 1)
        have e2 : ‖(‖τ‖ : ℝ) ^ (m + 1)‖ = ‖τ‖ ^ (m + 1) := by
          rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg (norm_nonneg τ)]
        rw [e1, e2]
      exact h1.trans h2
    have hm1 : m + 1 ≠ 0 := Nat.succ_ne_zero m
    have hP0 := hBigO.eq_zero_of_norm_pow hm1
    have ha0 : a 0 = 0 := by
      -- hP0 : ∑ j ∈ Finset.range (m + 1 + 1), 0 ^ j • a j = 0
      -- The sum at τ=0 simplifies to a 0.
      simp [Finset.sum_range_succ'] at hP0
      exact hP0
    -- Step B: factor `τ` out.
    set b : ℕ → 𝔸 := fun j => a (j + 1) with hb_def
    have hsum_factor : ∀ τ : ℝ,
        ∑ j ∈ Finset.range (m + 1 + 1), τ ^ j • a j =
          τ • ∑ j ∈ Finset.range (m + 1), τ ^ j • b j := by
      intro τ
      rw [Finset.sum_range_succ']
      simp only [pow_zero, one_smul, ha0, add_zero]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [b]
      rw [smul_smul, ← pow_succ']
    have hshift_aux :
        (fun τ : ℝ => τ • ∑ j ∈ Finset.range (m + 1), τ ^ j • b j) =o[𝓝 0]
          fun τ : ℝ => τ ^ (m + 1) := by
      refine h.congr' ?_ (Filter.EventuallyEq.refl _ _)
      filter_upwards with τ
      exact hsum_factor τ
    -- Step C: on punctured nbd, divide by τ.
    have hshift_ne :
        (fun τ : ℝ => ∑ j ∈ Finset.range (m + 1), τ ^ j • b j) =o[𝓝[≠] (0 : ℝ)]
          fun τ : ℝ => τ ^ m := by
      rw [isLittleO_iff]
      intro ε hε
      have hbnd_nhds := hshift_aux.def hε
      have hbnd_nhdsNE : ∀ᶠ τ : ℝ in 𝓝[≠] 0,
          ‖τ • ∑ j ∈ Finset.range (m + 1), τ ^ j • b j‖ ≤ ε * ‖τ ^ (m + 1)‖ :=
        hbnd_nhds.filter_mono nhdsWithin_le_nhds
      have hne : ∀ᶠ τ : ℝ in 𝓝[≠] 0, τ ≠ 0 := self_mem_nhdsWithin
      filter_upwards [hbnd_nhdsNE, hne] with τ hτ hne
      have hτnorm : ‖τ‖ > 0 := by
        rw [Real.norm_eq_abs]; exact abs_pos.mpr hne
      have hsmul : ‖τ • (∑ j ∈ Finset.range (m + 1), τ ^ j • b j)‖ =
          ‖τ‖ * ‖∑ j ∈ Finset.range (m + 1), τ ^ j • b j‖ := by rw [norm_smul]
      have hpow_succ : ‖τ ^ (m + 1)‖ = ‖τ‖ * ‖τ ^ m‖ := by
        rw [pow_succ, norm_mul, mul_comm]
      rw [hsmul, hpow_succ] at hτ
      have hτ' : ‖τ‖ * ‖∑ j ∈ Finset.range (m + 1), τ ^ j • b j‖ ≤
                  ‖τ‖ * (ε * ‖τ ^ m‖) := by linarith
      exact (mul_le_mul_iff_of_pos_left hτnorm).mp hτ'
    -- Step D: extend to 𝓝 0 via continuity.
    have hcont_sum : ContinuousAt (fun τ : ℝ => ∑ j ∈ Finset.range (m + 1), τ ^ j • b j) 0 :=
      (continuous_sum_smul_pow m b).continuousAt
    have hshift := isLittleO_of_nhdsNE_of_continuousAt hcont_sum hshift_ne
    -- Apply IH.
    have hb_zero := ih b hshift
    intro j hj
    match j, hj with
    | 0, _ => exact ha0
    | j' + 1, hj' =>
      have hj'' : j' ≤ m := Nat.succ_le_succ_iff.mp hj'
      have : a (j' + 1) = b j' := rfl
      rw [this]
      exact hb_zero j' hj''

/-! ### Main results -/

/-- **Corollary: vanishing from norm bound near `0`.**

If `h : ℝ → 𝔸` is `ContDiff ℝ k` and satisfies `‖h τ‖ ≤ C · |τ|^{k+1}` on a
neighbourhood of `0`, then all iterated derivatives of `h` at `0` up to order
`k` vanish. -/
lemma iteratedDeriv_eq_zero_of_norm_le_pow
    {𝔸 : Type*} [NormedAddCommGroup 𝔸] [NormedSpace ℝ 𝔸]
    {h : ℝ → 𝔸} {k : ℕ} (hCD : ContDiff ℝ k h)
    {C δ : ℝ} (hδ : 0 < δ)
    (h_bound : ∀ τ : ℝ, |τ| < δ → ‖h τ‖ ≤ C * |τ| ^ (k + 1)) :
    ∀ j, j ≤ k → iteratedDeriv j h 0 = 0 := by
  -- Step 1: `h =o[𝓝 0] (fun τ => τ^k)`.
  have h_bigO_pow : h =O[𝓝 0] fun τ : ℝ => τ ^ (k + 1) := by
    refine IsBigO.of_bound |C| ?_
    have h_ball : Set.Ioo (-δ) δ ∈ 𝓝 (0 : ℝ) :=
      Ioo_mem_nhds (by linarith) hδ
    filter_upwards [h_ball] with τ hτ
    have hτabs : |τ| < δ := by rw [abs_lt]; exact hτ
    have hbnd : ‖h τ‖ ≤ C * |τ| ^ (k + 1) := h_bound τ hτabs
    have h_pow_nn : 0 ≤ |τ| ^ (k + 1) := by positivity
    have hCabs : C * |τ| ^ (k + 1) ≤ |C| * |τ| ^ (k + 1) := by
      exact mul_le_mul_of_nonneg_right (le_abs_self C) h_pow_nn
    have hnorm_eq : |τ| ^ (k + 1) = ‖τ ^ (k + 1)‖ := by
      simp [Real.norm_eq_abs]
    calc ‖h τ‖
        ≤ C * |τ| ^ (k + 1) := hbnd
      _ ≤ |C| * |τ| ^ (k + 1) := hCabs
      _ = |C| * ‖τ ^ (k + 1)‖ := by rw [hnorm_eq]
  have h_littleO : h =o[𝓝 0] fun τ : ℝ => τ ^ k := by
    have h_pow : (fun τ : ℝ => τ ^ (k + 1)) =o[𝓝 0] fun τ : ℝ => τ ^ k :=
      isLittleO_pow_pow (Nat.lt_succ_self k)
    exact h_bigO_pow.trans_isLittleO h_pow
  -- Step 2: taylor_isLittleO_univ gives `h - taylorPoly =o τ^k`.
  have h_taylor_lo :
      (fun τ : ℝ => h τ - taylorWithinEval h k univ 0 τ) =o[𝓝 0]
        fun τ : ℝ => (τ - 0) ^ k :=
    taylor_isLittleO_univ hCD
  have h_taylor_lo' :
      (fun τ : ℝ => h τ - taylorWithinEval h k univ 0 τ) =o[𝓝 0]
        fun τ : ℝ => τ ^ k := by
    simpa using h_taylor_lo
  -- Step 3: taylorWithinEval h k univ 0 =o[𝓝 0] τ^k.
  have h_poly_lo :
      (fun τ : ℝ => taylorWithinEval h k univ 0 τ) =o[𝓝 0] fun τ : ℝ => τ ^ k := by
    have hrw : (fun τ : ℝ => taylorWithinEval h k univ 0 τ) =
               fun τ : ℝ => h τ - (h τ - taylorWithinEval h k univ 0 τ) := by
      funext τ; abel
    rw [hrw]
    exact h_littleO.sub h_taylor_lo'
  -- Step 4: rewrite taylorWithinEval as the explicit sum.
  have h_poly_explicit :
      (fun τ : ℝ => taylorWithinEval h k univ 0 τ) =
        fun τ : ℝ => ∑ j ∈ Finset.range (k + 1),
          τ ^ j • ((Nat.factorial j : ℝ)⁻¹ • iteratedDeriv j h 0) := by
    funext τ
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [sub_zero, iteratedDerivWithin_univ, mul_comm, mul_smul]
  rw [h_poly_explicit] at h_poly_lo
  -- Step 5: polynomial uniqueness.
  set c : ℕ → 𝔸 := fun j => (Nat.factorial j : ℝ)⁻¹ • iteratedDeriv j h 0 with hc_def
  have hc_zero := sum_smul_pow_eq_zero_of_isLittleO c h_poly_lo
  -- Step 6: extract iteratedDeriv from c j = 0.
  intro j hj
  have hc_j := hc_zero j hj
  have h_fact_ne : ((Nat.factorial j : ℝ))⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact_mod_cast Nat.factorial_pos j |>.ne'
  exact (smul_eq_zero.mp hc_j).resolve_left h_fact_ne

/-- **Main: Taylor-match from norm bound.**

If `f, g : ℝ → 𝔸` are `ContDiff ℝ k` and agree to order `k+1` near `0`
(i.e., `‖f τ - g τ‖ ≤ C · |τ|^{k+1}` on a neighbourhood of `0`), then
their iterated derivatives at `0` match for all orders `j ≤ k`. -/
lemma iteratedDeriv_eq_of_norm_le_pow
    {𝔸 : Type*} [NormedAddCommGroup 𝔸] [NormedSpace ℝ 𝔸]
    {f g : ℝ → 𝔸} {k : ℕ}
    (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g)
    {C δ : ℝ} (hδ : 0 < δ)
    (h_bound : ∀ τ : ℝ, |τ| < δ → ‖f τ - g τ‖ ≤ C * |τ| ^ (k + 1)) :
    ∀ j, j ≤ k → iteratedDeriv j f 0 = iteratedDeriv j g 0 := by
  intro j hj
  have h_CD : ContDiff ℝ k (f - g) := hf.sub hg
  have h_bnd' : ∀ τ : ℝ, |τ| < δ → ‖(f - g) τ‖ ≤ C * |τ| ^ (k + 1) := by
    intro τ hτ
    simpa [Pi.sub_apply] using h_bound τ hτ
  have h_zero := iteratedDeriv_eq_zero_of_norm_le_pow h_CD hδ h_bnd' j hj
  have hf_CDA : ContDiffAt ℝ j f 0 := (hf.of_le (by exact_mod_cast hj)).contDiffAt
  have hg_CDA : ContDiffAt ℝ j g 0 := (hg.of_le (by exact_mod_cast hj)).contDiffAt
  rw [iteratedDeriv_sub hf_CDA hg_CDA] at h_zero
  exact sub_eq_zero.mp h_zero

end
