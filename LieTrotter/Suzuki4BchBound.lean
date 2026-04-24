/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Single-step BCH O(|τ|⁵) bound for the Suzuki 5-block product

Closes the S₄ Form-B bound

  ‖s4Func A B p τ - exp(τ•(A+B))‖ ≤ C · |τ|⁵

for `|τ| < δ`, under `IsSuzukiCubic p`.  Uses Lean-BCH's M6 single-step bound,
with the regime established via `Tendsto.eventually_lt_const`.
-/

import LieTrotter.Suzuki4HasDerivAt
import BCH.Palindromic

noncomputable section

open NormedSpace Filter Topology

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-! ## Bridge: `s4Func = BCH.suzuki5Product` -/

lemma s4Func_eq_suzuki5Product (A B : 𝔸) (p τ : ℝ) :
    s4Func A B p τ = BCH.suzuki5Product (𝕂 := ℝ) A B p τ := rfl

/-! ## Simple tendsto → 0 lemmas -/

section TendstoZero

variable (A B : 𝔸) (p : ℝ)

/-- `suzuki5ArgNormBound A B p τ → 0` as τ → 0. -/
lemma tendsto_suzuki5ArgNormBound_zero :
    Tendsto (fun τ : ℝ => BCH.suzuki5ArgNormBound (𝕂 := ℝ) A B p τ) (𝓝 0) (𝓝 0) := by
  have hcont : Continuous (fun τ : ℝ => BCH.suzuki5ArgNormBound (𝕂 := ℝ) A B p τ) := by
    unfold BCH.suzuki5ArgNormBound
    exact (continuous_norm.comp continuous_id).mul continuous_const
  have h := hcont.tendsto 0
  have : BCH.suzuki5ArgNormBound (𝕂 := ℝ) A B p 0 = 0 := by
    unfold BCH.suzuki5ArgNormBound; simp
  rw [this] at h
  exact h

/-- `‖(c*τ)•A‖ + ‖(c*τ)•B‖ → 0` as τ → 0. -/
lemma tendsto_argNormPair_zero (c : ℝ) :
    Tendsto (fun τ : ℝ => ‖(c * τ) • A‖ + ‖(c * τ) • B‖) (𝓝 0) (𝓝 0) := by
  have h1 : Continuous (fun τ : ℝ => (c * τ) • A) :=
    (continuous_const.mul continuous_id).smul continuous_const
  have h2 : Continuous (fun τ : ℝ => (c * τ) • B) :=
    (continuous_const.mul continuous_id).smul continuous_const
  have hcont : Continuous (fun τ : ℝ => ‖(c * τ) • A‖ + ‖(c * τ) • B‖) := h1.norm.add h2.norm
  have h := hcont.tendsto 0
  have heq : ‖((c * 0) • A : 𝔸)‖ + ‖((c * 0) • B : 𝔸)‖ = 0 := by simp
  rw [heq] at h
  exact h

/-- `‖τ•(A+B)‖ → 0` as τ → 0. -/
lemma tendsto_normSmulV_zero :
    Tendsto (fun τ : ℝ => ‖τ • (A + B)‖) (𝓝 0) (𝓝 0) := by
  have hcont : Continuous (fun τ : ℝ => ‖τ • (A + B)‖) :=
    (continuous_id.smul continuous_const).norm
  have h := hcont.tendsto 0
  have heq : ‖((0 : ℝ) • (A + B) : 𝔸)‖ = 0 := by simp
  rw [heq] at h
  exact h

end TendstoZero

/-! ## Bounding `‖strangBlock_log‖` for small τ -/

section StrangBlockLogBound

variable (A B : 𝔸)

/-- `‖strangBlock_log A B c τ‖ → 0` as τ → 0, via `BCH.norm_strangBlock_log_le`. -/
lemma tendsto_normStrangBlockLog_zero (c : ℝ) :
    Tendsto (fun τ : ℝ => ‖BCH.strangBlock_log ℝ A B c τ‖) (𝓝 0) (𝓝 0) := by
  have hargs := tendsto_argNormPair_zero A B c
  have hreg : ∀ᶠ τ : ℝ in 𝓝 0, ‖(c * τ) • A‖ + ‖(c * τ) • B‖ < 1 / 4 :=
    hargs.eventually_lt_const (by norm_num)
  -- Upper bound function
  have upper_cont : Continuous (fun τ : ℝ =>
      |c * τ| * (‖A‖ + ‖B‖) +
      (|c * τ| * (‖A‖ + ‖B‖)) ^ 3 +
      10000000 * (|c * τ| * (‖A‖ + ‖B‖)) ^ 5) := by
    have h1 : Continuous (fun τ : ℝ => |c * τ| * (‖A‖ + ‖B‖)) :=
      (continuous_const.mul continuous_id).abs.mul continuous_const
    exact (h1.add (h1.pow 3)).add (continuous_const.mul (h1.pow 5))
  have upper_tendsto : Tendsto (fun τ : ℝ =>
      |c * τ| * (‖A‖ + ‖B‖) +
      (|c * τ| * (‖A‖ + ‖B‖)) ^ 3 +
      10000000 * (|c * τ| * (‖A‖ + ‖B‖)) ^ 5) (𝓝 0) (𝓝 0) := by
    have h := upper_cont.tendsto 0
    have heq : |c * (0 : ℝ)| * (‖A‖ + ‖B‖) +
        (|c * 0| * (‖A‖ + ‖B‖)) ^ 3 +
        10000000 * (|c * 0| * (‖A‖ + ‖B‖)) ^ 5 = 0 := by simp
    rw [heq] at h
    exact h
  have hsqueeze : ∀ᶠ τ : ℝ in 𝓝 0,
      ‖BCH.strangBlock_log ℝ A B c τ‖ ≤
        |c * τ| * (‖A‖ + ‖B‖) +
        (|c * τ| * (‖A‖ + ‖B‖)) ^ 3 +
        10000000 * (|c * τ| * (‖A‖ + ‖B‖)) ^ 5 := by
    filter_upwards [hreg] with τ hτ
    have h' := BCH.norm_strangBlock_log_le (𝕂 := ℝ) A B c τ hτ
    simpa [Real.norm_eq_abs] using h'
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds upper_tendsto
    (Eventually.of_forall (fun τ => norm_nonneg _)) hsqueeze

/-- `‖(4:ℝ) • strangBlock_log A B c τ‖ → 0` as τ → 0. -/
lemma tendsto_norm_smul4_strangBlockLog_zero (c : ℝ) :
    Tendsto (fun τ : ℝ => ‖(4 : ℝ) • BCH.strangBlock_log ℝ A B c τ‖) (𝓝 0) (𝓝 0) := by
  have hbase := tendsto_normStrangBlockLog_zero A B c
  have hub : ∀ τ : ℝ, ‖(4 : ℝ) • BCH.strangBlock_log ℝ A B c τ‖ ≤
      4 * ‖BCH.strangBlock_log ℝ A B c τ‖ := by
    intro τ
    calc ‖(4 : ℝ) • BCH.strangBlock_log ℝ A B c τ‖
        ≤ ‖(4 : ℝ)‖ * ‖BCH.strangBlock_log ℝ A B c τ‖ := norm_smul_le _ _
      _ = 4 * ‖BCH.strangBlock_log ℝ A B c τ‖ := by
          rw [show ‖(4 : ℝ)‖ = 4 from by norm_num]
  have hupper : Tendsto (fun τ : ℝ => 4 * ‖BCH.strangBlock_log ℝ A B c τ‖) (𝓝 0) (𝓝 0) := by
    have h := hbase.const_mul 4
    simp at h
    exact h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
    (Eventually.of_forall (fun τ => norm_nonneg _))
    (Eventually.of_forall hub)

end StrangBlockLogBound

/-! ## Bounding `‖suzuki5_bch‖` for small τ -/

section Suzuki5BchBound

variable (A B : 𝔸) (p : ℝ)

/-- `‖suzuki5_bch ℝ A B p τ‖ → 0` as τ → 0, via M3b + triangle inequality. -/
lemma tendsto_normSuzuki5Bch_zero :
    Tendsto (fun τ : ℝ => ‖BCH.suzuki5_bch ℝ A B p τ‖) (𝓝 0) (𝓝 0) := by
  have hR := tendsto_suzuki5ArgNormBound_zero A B p
  have hregime : ∀ᶠ τ : ℝ in 𝓝 0,
      BCH.suzuki5ArgNormBound (𝕂 := ℝ) A B p τ < Real.log 2 :=
    hR.eventually_lt_const (Real.log_pos (by norm_num))
  -- Upper bound function
  have hexp_zero : Real.exp 0 = 1 := Real.exp_zero
  have texpR : Tendsto (fun τ : ℝ =>
      Real.exp (BCH.suzuki5ArgNormBound (𝕂 := ℝ) A B p τ)) (𝓝 0) (𝓝 1) := by
    have := Real.continuous_exp.tendsto 0
    rw [hexp_zero] at this
    exact this.comp hR
  have tτV := tendsto_normSmulV_zero A B
  have ha : Tendsto (fun τ : ℝ =>
      Real.exp (BCH.suzuki5ArgNormBound (𝕂 := ℝ) A B p τ) - 1) (𝓝 0) (𝓝 0) := by
    have h := texpR.sub_const 1
    simp at h
    exact h
  have t1 : Tendsto (fun τ : ℝ =>
      Real.exp (BCH.suzuki5ArgNormBound (𝕂 := ℝ) A B p τ) - 1 -
        BCH.suzuki5ArgNormBound (𝕂 := ℝ) A B p τ) (𝓝 0) (𝓝 0) := by
    have := ha.sub hR
    simp at this
    exact this
  have t2 : Tendsto (fun τ : ℝ =>
      (Real.exp (BCH.suzuki5ArgNormBound (𝕂 := ℝ) A B p τ) - 1) ^ 2 /
        (2 - Real.exp (BCH.suzuki5ArgNormBound (𝕂 := ℝ) A B p τ))) (𝓝 0) (𝓝 0) := by
    have num : Tendsto (fun τ : ℝ =>
        (Real.exp (BCH.suzuki5ArgNormBound (𝕂 := ℝ) A B p τ) - 1) ^ 2) (𝓝 0) (𝓝 0) := by
      have := ha.pow 2
      simp at this
      exact this
    have hden_tendsto : Tendsto (fun τ : ℝ =>
        (2 : ℝ) - Real.exp (BCH.suzuki5ArgNormBound (𝕂 := ℝ) A B p τ))
        (𝓝 0) (𝓝 ((2 : ℝ) - 1)) :=
      tendsto_const_nhds.sub texpR
    have hden_ne : ((2 : ℝ) - 1) ≠ 0 := by norm_num
    have := num.div hden_tendsto hden_ne
    simp at this
    exact this
  have tupper : Tendsto (fun τ : ℝ =>
      ‖τ • (A + B)‖ +
      ((Real.exp (BCH.suzuki5ArgNormBound (𝕂 := ℝ) A B p τ) - 1 -
          BCH.suzuki5ArgNormBound (𝕂 := ℝ) A B p τ) +
        (Real.exp (BCH.suzuki5ArgNormBound (𝕂 := ℝ) A B p τ) - 1) ^ 2 /
          (2 - Real.exp (BCH.suzuki5ArgNormBound (𝕂 := ℝ) A B p τ)))) (𝓝 0) (𝓝 0) := by
    have h := tτV.add (t1.add t2)
    -- h : Tendsto ... (𝓝 (0 + (0 + 0)))
    have : (0 : ℝ) + (0 + 0) = 0 := by ring
    rw [this] at h
    exact h
  have hsqueeze : ∀ᶠ τ : ℝ in 𝓝 0,
      ‖BCH.suzuki5_bch ℝ A B p τ‖ ≤
      ‖τ • (A + B)‖ +
      ((Real.exp (BCH.suzuki5ArgNormBound (𝕂 := ℝ) A B p τ) - 1 -
          BCH.suzuki5ArgNormBound (𝕂 := ℝ) A B p τ) +
        (Real.exp (BCH.suzuki5ArgNormBound (𝕂 := ℝ) A B p τ) - 1) ^ 2 /
          (2 - Real.exp (BCH.suzuki5ArgNormBound (𝕂 := ℝ) A B p τ))) := by
    filter_upwards [hregime] with τ hτ
    have hm3b := BCH.norm_suzuki5_bch_sub_smul_le (𝕂 := ℝ) A B p τ hτ
    have htri : ‖BCH.suzuki5_bch ℝ A B p τ‖ ≤
        ‖BCH.suzuki5_bch ℝ A B p τ - τ • (A + B)‖ + ‖τ • (A + B)‖ := by
      calc ‖BCH.suzuki5_bch ℝ A B p τ‖
          = ‖(BCH.suzuki5_bch ℝ A B p τ - τ • (A + B)) + τ • (A + B)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds tupper
    (Eventually.of_forall (fun τ => norm_nonneg _)) hsqueeze

end Suzuki5BchBound

/-! ## Bounding the nested `bch` quantity -/

section NestedBchBound

/-- If `f → 0` and `g → 0`, then `‖bch(f, g)‖ → 0`. -/
private lemma tendsto_normBch_zero_of_tendsto {α : Type*} {l : Filter α}
    {f g : α → 𝔸} (hf : Tendsto f l (𝓝 0)) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x => ‖BCH.bch (𝕂 := ℝ) (f x) (g x)‖) l (𝓝 0) := by
  have hnormf : Tendsto (fun x => ‖f x‖) l (𝓝 0) := by
    have hc : Continuous (fun a : 𝔸 => ‖a‖) := continuous_norm
    have h := hc.tendsto (0 : 𝔸)
    rw [norm_zero] at h
    exact h.comp hf
  have hnormg : Tendsto (fun x => ‖g x‖) l (𝓝 0) := by
    have hc : Continuous (fun a : 𝔸 => ‖a‖) := continuous_norm
    have h := hc.tendsto (0 : 𝔸)
    rw [norm_zero] at h
    exact h.comp hg
  have hsum : Tendsto (fun x => ‖f x‖ + ‖g x‖) l (𝓝 0) := by
    have := hnormf.add hnormg
    simp at this
    exact this
  have hregime : ∀ᶠ x in l, ‖f x‖ + ‖g x‖ < Real.log 2 :=
    hsum.eventually_lt_const (Real.log_pos (by norm_num))
  have hexp_zero : Real.exp 0 = 1 := Real.exp_zero
  have hexpsum : Tendsto (fun x => Real.exp (‖f x‖ + ‖g x‖)) l (𝓝 1) := by
    have hc := Real.continuous_exp.tendsto 0
    rw [hexp_zero] at hc
    exact hc.comp hsum
  have hsq : Tendsto (fun x => 3 * (‖f x‖ + ‖g x‖) ^ 2) l (𝓝 0) := by
    have := (hsum.pow 2).const_mul 3
    simp at this
    exact this
  have hden : Tendsto (fun x => (2 : ℝ) - Real.exp (‖f x‖ + ‖g x‖)) l (𝓝 ((2 : ℝ) - 1)) :=
    tendsto_const_nhds.sub hexpsum
  have hden_ne : ((2 : ℝ) - 1) ≠ 0 := by norm_num
  have hquot : Tendsto (fun x =>
      3 * (‖f x‖ + ‖g x‖) ^ 2 / (2 - Real.exp (‖f x‖ + ‖g x‖))) l (𝓝 0) := by
    have := hsq.div hden hden_ne
    simp at this
    exact this
  have tupper : Tendsto (fun x =>
      ‖f x‖ + ‖g x‖ +
      3 * (‖f x‖ + ‖g x‖) ^ 2 / (2 - Real.exp (‖f x‖ + ‖g x‖))) l (𝓝 0) := by
    have := hsum.add hquot
    simp at this
    exact this
  have hsqueeze : ∀ᶠ x in l,
      ‖BCH.bch (𝕂 := ℝ) (f x) (g x)‖ ≤
      ‖f x‖ + ‖g x‖ +
      3 * (‖f x‖ + ‖g x‖) ^ 2 / (2 - Real.exp (‖f x‖ + ‖g x‖)) := by
    filter_upwards [hregime] with x hx
    have hsub := BCH.norm_bch_sub_add_le (𝕂 := ℝ) (f x) (g x) hx
    have hAB : ‖f x + g x‖ ≤ ‖f x‖ + ‖g x‖ := norm_add_le _ _
    calc ‖BCH.bch (𝕂 := ℝ) (f x) (g x)‖
        = ‖(BCH.bch (𝕂 := ℝ) (f x) (g x) - (f x + g x)) + (f x + g x)‖ := by congr 1; abel
      _ ≤ ‖BCH.bch (𝕂 := ℝ) (f x) (g x) - (f x + g x)‖ + ‖f x + g x‖ := norm_add_le _ _
      _ ≤ 3 * (‖f x‖ + ‖g x‖) ^ 2 / (2 - Real.exp (‖f x‖ + ‖g x‖)) + (‖f x‖ + ‖g x‖) := by
          linarith
      _ = ‖f x‖ + ‖g x‖ + 3 * (‖f x‖ + ‖g x‖) ^ 2 / (2 - Real.exp (‖f x‖ + ‖g x‖)) := by ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds tupper
    (Eventually.of_forall (fun x => norm_nonneg _)) hsqueeze

/-- If `‖f‖ → 0`, then `f → 0`. -/
private lemma tendsto_of_tendsto_norm_zero {α : Type*} {l : Filter α}
    {f : α → 𝔸} (h : Tendsto (fun x => ‖f x‖) l (𝓝 0)) : Tendsto f l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact h

variable (A B : 𝔸) (p : ℝ)

/-- `‖nested_bch‖ → 0` as τ → 0. -/
lemma tendsto_normNestedBch_zero :
    Tendsto
      (fun τ : ℝ => ‖BCH.bch (𝕂 := ℝ)
        (BCH.bch (𝕂 := ℝ)
          ((2 : ℝ)⁻¹ • ((4 : ℝ) • BCH.strangBlock_log ℝ A B p τ))
          (BCH.strangBlock_log ℝ A B (1 - 4 * p) τ))
        ((2 : ℝ)⁻¹ • ((4 : ℝ) • BCH.strangBlock_log ℝ A B p τ))‖)
      (𝓝 0) (𝓝 0) := by
  have hX : Tendsto (fun τ : ℝ => BCH.strangBlock_log ℝ A B p τ) (𝓝 0) (𝓝 0) :=
    tendsto_of_tendsto_norm_zero (tendsto_normStrangBlockLog_zero A B p)
  have hY : Tendsto (fun τ : ℝ => BCH.strangBlock_log ℝ A B (1 - 4 * p) τ) (𝓝 0) (𝓝 0) :=
    tendsto_of_tendsto_norm_zero (tendsto_normStrangBlockLog_zero A B (1 - 4 * p))
  have h4X : Tendsto (fun τ : ℝ => (4 : ℝ) • BCH.strangBlock_log ℝ A B p τ) (𝓝 0) (𝓝 0) := by
    have h := hX.const_smul (4 : ℝ)
    simp at h
    exact h
  have hhalfX : Tendsto (fun τ : ℝ =>
      ((2 : ℝ)⁻¹ • ((4 : ℝ) • BCH.strangBlock_log ℝ A B p τ))) (𝓝 0) (𝓝 0) := by
    have h := h4X.const_smul ((2 : ℝ)⁻¹)
    simp at h
    exact h
  have hinner_norm := tendsto_normBch_zero_of_tendsto hhalfX hY
  have hinner : Tendsto (fun τ : ℝ => BCH.bch (𝕂 := ℝ)
      ((2 : ℝ)⁻¹ • ((4 : ℝ) • BCH.strangBlock_log ℝ A B p τ))
      (BCH.strangBlock_log ℝ A B (1 - 4 * p) τ)) (𝓝 0) (𝓝 0) :=
    tendsto_of_tendsto_norm_zero hinner_norm
  exact tendsto_normBch_zero_of_tendsto hinner hhalfX

end NestedBchBound

/-! ## Existence of the M4b regime on a nbhd of 0 -/

/-- All six M4b regime quantities are `< threshold` on some nbhd of τ = 0. -/
lemma exists_regime_nhds (A B : 𝔸) (p : ℝ) :
    ∀ᶠ τ : ℝ in 𝓝 0,
      BCH.suzuki5ArgNormBound (𝕂 := ℝ) A B p τ < Real.log 2 ∧
      ‖(p * τ) • A‖ + ‖(p * τ) • B‖ < 1 / 4 ∧
      ‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖ < 1 / 4 ∧
      ‖(4 : ℝ) • BCH.strangBlock_log ℝ A B p τ‖ +
        ‖BCH.strangBlock_log ℝ A B (1 - 4 * p) τ‖ < 1 / 4 ∧
      ‖BCH.suzuki5_bch ℝ A B p τ‖ < Real.log 2 ∧
      ‖BCH.bch (𝕂 := ℝ)
        (BCH.bch (𝕂 := ℝ)
          ((2 : ℝ)⁻¹ • ((4 : ℝ) • BCH.strangBlock_log ℝ A B p τ))
          (BCH.strangBlock_log ℝ A B (1 - 4 * p) τ))
        ((2 : ℝ)⁻¹ • ((4 : ℝ) • BCH.strangBlock_log ℝ A B p τ))‖ < Real.log 2 := by
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hquarter_pos : (0 : ℝ) < 1 / 4 := by norm_num
  have h1 := (tendsto_suzuki5ArgNormBound_zero A B p).eventually_lt_const hlog2_pos
  have h2 := (tendsto_argNormPair_zero A B p).eventually_lt_const hquarter_pos
  have h3 := (tendsto_argNormPair_zero A B (1 - 4 * p)).eventually_lt_const hquarter_pos
  have h4 : ∀ᶠ τ : ℝ in 𝓝 0,
      ‖(4 : ℝ) • BCH.strangBlock_log ℝ A B p τ‖ +
        ‖BCH.strangBlock_log ℝ A B (1 - 4 * p) τ‖ < 1 / 4 := by
    have t4X := tendsto_norm_smul4_strangBlockLog_zero A B p
    have tY := tendsto_normStrangBlockLog_zero A B (1 - 4 * p)
    have tsum : Tendsto (fun τ : ℝ =>
        ‖(4 : ℝ) • BCH.strangBlock_log ℝ A B p τ‖ +
          ‖BCH.strangBlock_log ℝ A B (1 - 4 * p) τ‖) (𝓝 0) (𝓝 0) := by
      have h := t4X.add tY
      simp at h
      exact h
    exact tsum.eventually_lt_const hquarter_pos
  have h5 := (tendsto_normSuzuki5Bch_zero A B p).eventually_lt_const hlog2_pos
  have h6 := (tendsto_normNestedBch_zero A B p).eventually_lt_const hlog2_pos
  filter_upwards [h1, h2, h3, h4, h5, h6] with τ h1τ h2τ h3τ h4τ h5τ h6τ
  exact ⟨h1τ, h2τ, h3τ, h4τ, h5τ, h6τ⟩

/-! ## The main theorem (Form B)

Uses Lean-BCH's `norm_s4Func_sub_exp_le_of_IsSuzukiCubic` (single-step bound at
`n = 1`) combined with the new opaque-RHS payoff lemma
`suzuki5_bch_M4b_RHS_le_t5_of_IsSuzukiCubic` (Lean-BCH commit `4ea6357`),
which encapsulates the polynomial bookkeeping inside the BCH library.

**Status (2026-04-24):** SLICE 1 is now sorry-free on the Lean-Trotter side.
The transitive sorry has migrated to Lean-BCH's `suzuki5_bch_M4b_RHS_le_t5_of_IsSuzukiCubic`
(an arithmetic-bookkeeping target on a single explicit polynomial).
-/

/-! ### Single-step BCH-derived O(|τ|⁵) bound -/

/-- **Form B**: single-step BCH-derived O(|τ|⁵) bound for the Suzuki 5-block product.

Under `IsSuzukiCubic p`, there exists `δ > 0` and `C ≥ 0` such that for all `|τ| < δ`,

  ‖s4Func A B p τ - exp(τ•(A+B))‖ ≤ C · |τ|⁵.

The proof composes:
- `BCH.norm_s4Func_sub_exp_le_of_IsSuzukiCubic` (single-step bound at `n=1`),
- `BCH.suzuki5_bch_M4b_RHS_le_t5_of_IsSuzukiCubic` (the new opaque-RHS payoff
  lemma in Lean-BCH commit `4ea6357`).

The polynomial bookkeeping that previously lived here has been pushed inside
the BCH library, where it is bounded once and for all on the opaque def
`suzuki5_bch_M4b_RHS`. -/
theorem exists_norm_s4Func_sub_exp_le_t5
    (A B : 𝔸) (p : ℝ) (hSuzuki : BCH.IsSuzukiCubic p) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ τ : ℝ, |τ| < δ →
      ‖s4Func A B p τ - exp (τ • (A + B))‖ ≤ C * |τ|^5 := by
  -- Step 1: the BCH M4b RHS is bounded by `K · |τ|^5` near 0.
  obtain ⟨δ_M, hδ_M_pos, K, hK_nn, h_M4b_le⟩ :=
    BCH.suzuki5_bch_M4b_RHS_le_t5_of_IsSuzukiCubic
      (𝕂 := ℝ) A B p hSuzuki
  -- Step 2: the 6 regime hypotheses required by `norm_s4Func_sub_exp_le_of_IsSuzukiCubic`
  -- hold on a nbhd of 0.
  have hregime := exists_regime_nhds A B p
  rw [Metric.eventually_nhds_iff] at hregime
  obtain ⟨δ_R, hδ_R_pos, hregime⟩ := hregime
  -- Step 3: take δ := min δ_M δ_R 1.
  set δ := min δ_M (min δ_R 1) with hδ_def
  have hδ_pos : 0 < δ := lt_min hδ_M_pos (lt_min hδ_R_pos (by norm_num : (0:ℝ) < 1))
  have hδ_le_M : δ ≤ δ_M := min_le_left _ _
  have hδ_le_R : δ ≤ δ_R := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ_le_one : δ ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
  -- Step 4: define C := K · exp(s + K), where s := ‖A‖ + ‖B‖.
  set s := ‖A‖ + ‖B‖ with hs_def
  have hs_nn : 0 ≤ s := by show (0:ℝ) ≤ ‖A‖ + ‖B‖; positivity
  set C := K * Real.exp (s + K) with hC_def
  have hExp_pos : 0 < Real.exp (s + K) := Real.exp_pos _
  have hC_nn : 0 ≤ C := mul_nonneg hK_nn hExp_pos.le
  refine ⟨δ, hδ_pos, C, hC_nn, ?_⟩
  intro τ hτ_lt
  have habsτ_nn : 0 ≤ |τ| := abs_nonneg _
  have hτ_le_one : |τ| ≤ 1 := le_trans hτ_lt.le hδ_le_one
  have hτ_lt_M : |τ| < δ_M := lt_of_lt_of_le hτ_lt hδ_le_M
  have hτ_lt_R : |τ| < δ_R := lt_of_lt_of_le hτ_lt hδ_le_R
  -- Step 5: extract the regime hypotheses at this τ.
  have hτ_dist : dist τ 0 < δ_R := by rw [Real.dist_eq]; simpa using hτ_lt_R
  obtain ⟨h_R, h_pτ, h_1m4pτ, h_regsb, h_Zbch, h_nested⟩ := hregime hτ_dist
  -- Step 6: the M4b RHS is ≤ K · |τ|^5.
  have h_τnorm : ‖(τ : ℝ)‖ = |τ| := Real.norm_eq_abs τ
  have h_M4b_τ : BCH.suzuki5_bch_M4b_RHS ℝ A B p τ ≤ K * |τ|^5 := by
    have h := h_M4b_le τ (by rw [h_τnorm]; exact hτ_lt_M)
    rw [h_τnorm] at h
    exact h
  -- Step 7: apply M6 at n=1, t=τ.
  have h_1_ne : (1 : ℕ) ≠ 0 := one_ne_zero
  have h_τdiv : (τ / (1 : ℕ) : ℝ) = τ := by simp
  have hR_at_τ : BCH.suzuki5ArgNormBound (𝕂 := ℝ) A B p (τ / (1 : ℕ)) < Real.log 2 := by
    rw [h_τdiv]; exact h_R
  have hp_at_τ : ‖(p * (τ / (1 : ℕ))) • A‖ + ‖(p * (τ / (1 : ℕ))) • B‖ < 1 / 4 := by
    rw [h_τdiv]; exact h_pτ
  have h1m4p_at_τ : ‖((1 - 4 * p) * (τ / (1 : ℕ))) • A‖ +
      ‖((1 - 4 * p) * (τ / (1 : ℕ))) • B‖ < 1 / 4 := by
    rw [h_τdiv]; exact h_1m4pτ
  have hreg_at_τ : ‖(4 : ℝ) • BCH.strangBlock_log ℝ A B p (τ / (1 : ℕ))‖ +
      ‖BCH.strangBlock_log ℝ A B (1 - 4 * p) (τ / (1 : ℕ))‖ < 1 / 4 := by
    rw [h_τdiv]; exact h_regsb
  have hZ1_at_τ : ‖BCH.suzuki5_bch ℝ A B p (τ / (1 : ℕ))‖ < Real.log 2 := by
    rw [h_τdiv]; exact h_Zbch
  have hZ2_at_τ : ‖BCH.bch (𝕂 := ℝ)
      (BCH.bch (𝕂 := ℝ)
        ((2 : ℝ)⁻¹ • ((4 : ℝ) • BCH.strangBlock_log ℝ A B p (τ / (1 : ℕ))))
        (BCH.strangBlock_log ℝ A B (1 - 4 * p) (τ / (1 : ℕ))))
      ((2 : ℝ)⁻¹ • ((4 : ℝ) • BCH.strangBlock_log ℝ A B p (τ / (1 : ℕ))))‖ < Real.log 2 := by
    rw [h_τdiv]; exact h_nested
  have hM6 := BCH.norm_s4Func_sub_exp_le_of_IsSuzukiCubic (𝕂 := ℝ) A B p τ 1 h_1_ne
    hSuzuki hR_at_τ hp_at_τ h1m4p_at_τ hreg_at_τ hZ1_at_τ hZ2_at_τ
  -- Rewrite BCH.s4Func ℝ A B p (τ/1) 1 = s4Func A B p τ.
  have h_s4Func_eq : BCH.s4Func ℝ A B p (τ / (1 : ℕ)) 1 = s4Func A B p τ := by
    unfold BCH.s4Func
    rw [h_τdiv, pow_one]
    exact (s4Func_eq_suzuki5Product A B p τ).symm
  rw [h_s4Func_eq] at hM6
  -- Step 8: collapse `(1 : ℕ) : ℝ` factor and `τ/↑1`. After these simplifications,
  -- hM6 takes the form `‖...‖ ≤ R · exp(‖τ•V‖ + R)` with `R := suzuki5_bch_M4b_RHS`.
  simp only [Nat.cast_one, one_mul, div_one] at hM6
  -- Now hM6 : ‖s4Func A B p τ - exp (τ • (A + B))‖ ≤
  --   suzuki5_bch_M4b_RHS ℝ A B p τ * exp (‖τ • (A+B)‖ + suzuki5_bch_M4b_RHS ℝ A B p τ).
  set R := BCH.suzuki5_bch_M4b_RHS ℝ A B p τ with hR_def
  -- R ≥ 0 (it's a sum of norm-pow terms; we derive nonnegativity from the bound).
  have hR_nn : 0 ≤ R := by
    have hτ5_nn : 0 ≤ |τ|^5 := by positivity
    have : 0 ≤ K * |τ|^5 := mul_nonneg hK_nn hτ5_nn
    -- The M6 LHS is a norm ≥ 0; split the product to get R ≥ 0.
    -- Actually simpler: derive R ≥ 0 directly from the M4b bound chain — we use the
    -- fact that the M4b RHS bound `‖suzuki5_bch - τ•V‖ ≤ R` forces `R ≥ 0`.
    have h_M4b_bound := BCH.norm_suzuki5_bch_sub_smul_le_of_IsSuzukiCubic
      (𝕂 := ℝ) A B p τ hSuzuki h_R h_pτ h_1m4pτ h_regsb h_Zbch h_nested
    exact le_trans (norm_nonneg _) h_M4b_bound
  have hτ5_nn : 0 ≤ |τ|^5 := by positivity
  have hτ5_le_one : |τ|^5 ≤ 1 := by
    calc |τ|^5 ≤ 1^5 := pow_le_pow_left₀ habsτ_nn hτ_le_one 5
      _ = 1 := by norm_num
  have hτV_norm : ‖τ • (A + B)‖ ≤ s := by
    have h1 : ‖τ • (A + B)‖ ≤ ‖(τ : ℝ)‖ * ‖A + B‖ := norm_smul_le _ _
    rw [h_τnorm] at h1
    have h_AB : ‖A + B‖ ≤ s := norm_add_le _ _
    have : |τ| * ‖A + B‖ ≤ 1 * s :=
      mul_le_mul hτ_le_one h_AB (norm_nonneg _) (by norm_num)
    linarith
  have hR_le_K : R ≤ K := by
    calc R ≤ K * |τ|^5 := h_M4b_τ
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left hτ5_le_one hK_nn
      _ = K := by ring
  have hexp_le : Real.exp (‖τ • (A + B)‖ + R) ≤ Real.exp (s + K) :=
    Real.exp_le_exp.mpr (by linarith)
  have hexp_pos : 0 < Real.exp (‖τ • (A + B)‖ + R) := Real.exp_pos _
  calc ‖s4Func A B p τ - exp (τ • (A + B))‖
      ≤ R * Real.exp (‖τ • (A + B)‖ + R) := hM6
    _ ≤ (K * |τ|^5) * Real.exp (s + K) := by
        apply mul_le_mul h_M4b_τ hexp_le hexp_pos.le
        exact mul_nonneg hK_nn hτ5_nn
    _ = C * |τ|^5 := by rw [hC_def]; ring

end
