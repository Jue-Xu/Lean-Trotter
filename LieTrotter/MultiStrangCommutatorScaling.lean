/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Multi-Operator Commutator-Scaling for Strang Splitting

The multi-operator commutator-scaling bound for the second-order Suzuki (Strang) formula,
generalizing `norm_strang_comm_scaling` (two operators) to Γ operators.

For anti-Hermitian operators in a C*-algebra:

  ‖palindromicProd [a₁,...,aₘ] - exp(∑ aᵢ)‖ ≤ listDoubleCommNorm [a₁,...,aₘ]

where `palindromicProd [a₁,...,aₘ] = exp(a₁/2)·exp(a₂/2)·⋯·exp(aₘ)·⋯·exp(a₂/2)·exp(a₁/2)`
is the symmetric (palindromic) product, and `listDoubleCommNorm` sums the double commutator
contributions `‖[Sᵢ,[Sᵢ,aᵢ]]‖/12 + ‖[aᵢ,[aᵢ,Sᵢ]]‖/24` with suffix sums `Sᵢ = ∑_{j>i} aⱼ`.

## Proof strategy

Induction on the list, same pattern as `MultiCommutatorScaling.lean`:
  palindromicProd (a :: rest) - exp(a + S) =
    exp(a/2) · (palindromicProd rest - exp S) · exp(a/2) +
    (exp(a/2) · exp(S) · exp(a/2) - exp(a + S))
Term 1 uses the inductive hypothesis; Term 2 uses `norm_strang_comm_scaling`.
-/

import LieTrotter.StrangCommutatorScaling

noncomputable section

open NormedSpace
open scoped BigOperators

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## Definition: Palindromic (symmetric) product
-/

/-- The palindromic product `exp(a₁/2)·⋯·exp(aₘ₋₁/2)·exp(aₘ)·exp(aₘ₋₁/2)·⋯·exp(a₁/2)`.
  This is the unscaled second-order Suzuki product (equivalent to `symmetricProd 1`). -/
def palindromicProd : List 𝔸 → 𝔸
  | [] => 1
  | [a] => exp a
  | a :: rest => exp ((1/2 : ℝ) • a) * palindromicProd rest * exp ((1/2 : ℝ) • a)

@[simp] lemma palindromicProd_nil : palindromicProd ([] : List 𝔸) = 1 := rfl

@[simp] lemma palindromicProd_singleton (a : 𝔸) : palindromicProd [a] = exp a := rfl

@[simp] lemma palindromicProd_cons_cons (a b : 𝔸) (rest : List 𝔸) :
    palindromicProd (a :: b :: rest) =
      exp ((1/2 : ℝ) • a) * palindromicProd (b :: rest) * exp ((1/2 : ℝ) • a) := rfl

/-!
## Definition: Double commutator norm with suffix sums
-/

/-- The sum of double commutator norms `∑ᵢ (‖[Sᵢ,[Sᵢ,aᵢ]]‖/12 + ‖[aᵢ,[aᵢ,Sᵢ]]‖/24)`
  where `Sᵢ = rest.sum` is the suffix sum after position i. -/
def listDoubleCommNorm : List 𝔸 → ℝ
  | [] => 0
  | a :: rest =>
      ‖rest.sum * (rest.sum * a - a * rest.sum) -
        (rest.sum * a - a * rest.sum) * rest.sum‖ / 12 +
      ‖a * (a * rest.sum - rest.sum * a) -
        (a * rest.sum - rest.sum * a) * a‖ / 24 +
      listDoubleCommNorm rest

@[simp] lemma listDoubleCommNorm_nil : listDoubleCommNorm ([] : List 𝔸) = 0 := rfl

lemma listDoubleCommNorm_nonneg (as : List 𝔸) : 0 ≤ listDoubleCommNorm as := by
  induction as with
  | nil => simp
  | cons a rest ih =>
    simp only [listDoubleCommNorm]
    have h1 := norm_nonneg (rest.sum * (rest.sum * a - a * rest.sum) -
      (rest.sum * a - a * rest.sum) * rest.sum)
    have h2 := norm_nonneg (a * (a * rest.sum - rest.sum * a) -
      (a * rest.sum - rest.sum * a) * a)
    linarith

/-!
## Algebraic decomposition for the palindromic product
-/

/-- The palindromic product error decomposes into an inner error (IH) and
  a two-operator Strang error. -/
private lemma palindromicProd_decomp (a : 𝔸) (rest : List 𝔸) (hne : rest ≠ []) :
    palindromicProd (a :: rest) - exp (a + rest.sum) =
      exp ((1/2 : ℝ) • a) * (palindromicProd rest - exp rest.sum) * exp ((1/2 : ℝ) • a) +
      (exp ((1/2 : ℝ) • a) * exp rest.sum * exp ((1/2 : ℝ) • a) - exp (a + rest.sum)) := by
  match rest, hne with
  | _ :: _, _ => simp only [palindromicProd_cons_cons]; noncomm_ring

/-!
## Main theorem: multi-operator Strang commutator-scaling bound
-/

variable [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]

/-- **Multi-operator commutator-scaling Strang error (anti-Hermitian case):**
  `‖palindromicProd [a₁,...,aₘ] - exp(∑ aᵢ)‖ ≤ listDoubleCommNorm [a₁,...,aₘ]`.

  Generalizes `norm_strang_comm_scaling` (two operators) to Γ operators.
  For anti-Hermitian operators in a C*-algebra, the error is O(t³) in the scaling
  parameter, with coefficients given by pairwise double commutator norms. -/
theorem norm_palindromicProd_sub_exp_sum_comm (as : List 𝔸)
    (hskew : ∀ a ∈ as, star a = -a) :
    ‖palindromicProd as - exp as.sum‖ ≤ listDoubleCommNorm as := by
  induction as with
  | nil => simp [exp_zero]
  | cons a rest ih =>
    by_cases hne : rest = []
    · subst hne; simp [exp_zero, palindromicProd, listDoubleCommNorm]
    · -- Setup
      have ha : star a = -a := hskew a (List.mem_cons.mpr (Or.inl rfl))
      have hrest : ∀ b ∈ rest, star b = -b :=
        fun b hb => hskew b (List.mem_cons.mpr (Or.inr hb))
      set S := rest.sum with hS_def
      have hS : star S = -S := by
        simp only [hS_def]
        suffices h : ∀ (l : List 𝔸), (∀ b ∈ l, star b = -b) → star l.sum = -l.sum from
          h rest hrest
        intro l hl; induction l with
        | nil => simp
        | cons c cs ih' =>
          simp only [List.sum_cons, star_add, neg_add]
          rw [hl c (List.mem_cons.mpr (Or.inl rfl)),
              ih' (fun b hb => hl b (List.mem_cons.mpr (Or.inr hb)))]
      letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
      -- Decompose the error
      simp only [List.sum_cons]
      rw [palindromicProd_decomp a rest hne]
      -- Term 1: exp(a/2) · (PP(rest) - exp S) · exp(a/2) — bounded by IH
      have h_ih := ih hrest
      have h_term1 : ‖exp ((1/2 : ℝ) • a) * (palindromicProd rest - exp S) *
          exp ((1/2 : ℝ) • a)‖ ≤ listDoubleCommNorm rest := by
        calc ‖exp ((1/2 : ℝ) • a) * (palindromicProd rest - exp S) *
              exp ((1/2 : ℝ) • a)‖
            ≤ ‖exp ((1/2 : ℝ) • a)‖ * ‖palindromicProd rest - exp S‖ *
                ‖exp ((1/2 : ℝ) • a)‖ := by
              calc _ ≤ ‖exp ((1/2 : ℝ) • a) * (palindromicProd rest - exp S)‖ *
                      ‖exp ((1/2 : ℝ) • a)‖ := norm_mul_le _ _
                _ ≤ _ := by gcongr; exact norm_mul_le _ _
          _ = ‖palindromicProd rest - exp S‖ := by
              rw [norm_exp_smul_of_skewAdjoint ha (1/2 : ℝ), one_mul, mul_one]
          _ ≤ listDoubleCommNorm rest := h_ih
      -- Term 2: exp(a/2) · exp(S) · exp(a/2) - exp(a+S) — bounded by norm_strang_comm_scaling
      -- This is the Strang error for the pair (a, S)
      have h_term2 : ‖exp ((1/2 : ℝ) • a) * exp S * exp ((1/2 : ℝ) • a) -
          exp (a + S)‖ ≤
        ‖S * (S * a - a * S) - (S * a - a * S) * S‖ / 12 +
        ‖a * (a * S - S * a) - (a * S - S * a) * a‖ / 24 := by
        -- Rewrite to match norm_strang_comm_scaling with t = 1
        have h := norm_strang_comm_scaling a S (zero_le_one) ha hS
        simp only [one_div, one_smul, mul_one, one_pow] at h
        -- The S in the Strang formula is "B", so the bound has [S,[S,a]]/12 + [a,[a,S]]/24
        convert h using 2
        · simp only [one_div]
      -- Combine
      calc ‖exp ((1/2 : ℝ) • a) * (palindromicProd rest - exp S) * exp ((1/2 : ℝ) • a) +
            (exp ((1/2 : ℝ) • a) * exp S * exp ((1/2 : ℝ) • a) - exp (a + S))‖
          ≤ ‖exp ((1/2 : ℝ) • a) * (palindromicProd rest - exp S) * exp ((1/2 : ℝ) • a)‖ +
            ‖exp ((1/2 : ℝ) • a) * exp S * exp ((1/2 : ℝ) • a) - exp (a + S)‖ :=
            norm_add_le _ _
        _ ≤ listDoubleCommNorm rest +
            (‖S * (S * a - a * S) - (S * a - a * S) * S‖ / 12 +
             ‖a * (a * S - S * a) - (a * S - S * a) * a‖ / 24) :=
            add_le_add h_term1 h_term2
        _ = listDoubleCommNorm (a :: rest) := by
            simp only [listDoubleCommNorm, hS_def]; ring

end
