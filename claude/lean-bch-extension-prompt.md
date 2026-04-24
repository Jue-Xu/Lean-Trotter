# Prompt: Extend Lean-BCH to close the 3 remaining Lean-Trotter BCH-interface axioms

## Context

**Lean-BCH** (https://github.com/Jue-Xu/Lean-BCH) provides the Baker-Campbell-Hausdorff
machinery used by **Lean-Trotter** (https://github.com/Jue-Xu/Lean-Trotter).
Lean-Trotter imports Lean-BCH as a Lake git dependency and is currently pinned
at rev `c71d8f2`.

Lean-BCH is **0-sorries** across all files. Lean-Trotter is **0-sorries** and
the headline theorems `bch_iteratedDeriv_s4Func_order4`,
`exists_norm_s4Func_sub_exp_le_t5`, and `lie_trotter` each depend only on
`[propext, Classical.choice, Quot.sound]`.

What remains: three **BCH-interface axioms** in
`LieTrotter/Suzuki4ViaBCH.lean` that encode 5-factor palindromic BCH facts
beyond Lean-BCH's current 2-factor quintic coverage. Each supports exactly
one L2/L3/L4 S₄ bound.

Your job: extend Lean-BCH so these axioms become theorems on the
Lean-Trotter side.

## Setup

Work in a local clone of Lean-BCH:

```bash
git clone https://github.com/Jue-Xu/Lean-BCH.git
cd Lean-BCH
# Branch off main at c71d8f2 (current Lean-Trotter pin)
git checkout -b trotter-5factor-palindromic
```

Build with:
```bash
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get
lake build
```

The reference Lean-Trotter repo is at
`/Users/jue/Documents/Claude/Projects/Lean-Trotter`. Inspect
`LieTrotter/Suzuki4ViaBCH.lean` to see the exact axiom statements you must
match.

## The 3 axioms and what they need

All three are stated over `𝔸 : Type*` with typeclasses
`[NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]`
plus the anti-Hermitian stack
`[StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]`.

### Axiom 1: `bch_w4Deriv_quintic_level2` (L2 — unit coefficients)

```lean
axiom bch_w4Deriv_quintic_level2
    (A B : 𝔸) (hA : star A = -A) (hB : star B = -B)
    (p : ℝ) (hcubic : IsSuzukiCubic p) (t : ℝ) (ht : 0 ≤ t) :
    ∀ τ ∈ Set.Icc (0 : ℝ) t,
      ‖w4Deriv A B p τ‖ ≤ (5 * bchFourFoldSum A B) * τ ^ 4
```

where
- `w4Deriv A B p τ` = derivative of `w₄(τ) = exp(-τ•(A+B)) · s4Func A B p τ`
  at `τ` (extracted via `Classical.choose` from Module 1 `hasDerivAt_w4`).
- `s4Func A B p τ` = the 11-factor Suzuki S₄ palindromic product.
- `IsSuzukiCubic p ↔ 4p³ + (1-4p)³ = 0`.
- `bchFourFoldSum A B = Σᵢ ‖Cᵢ‖` over the 8 Childs 4-fold commutators
  `childsComm₁ … childsComm₈` (unit coefficients).

**Mathematical content.** For Suzuki palindromic `p`, the BCH expansion of
`log(s4Func(τ))` at order τ⁵ projects onto the 8 Childs commutators with
bounded coefficients `βᵢ(p)` satisfying `|βᵢ(p)| ≤ 1`. Differentiating
`w₄(τ) = exp(-τH) · s4Func(τ)` and using the triangle inequality yields the
pointwise bound with **unit** coefficients on the 8 four-fold commutators.

**Closure path in Lean-BCH.** Extend Lean-BCH to the **5-factor palindromic
quintic remainder**: for the 5-block product
`S₄(τ) = strangBlock(p τ) · strangBlock(p τ) · strangBlock((1-4p) τ) · strangBlock(p τ) · strangBlock(p τ)`,
prove

```
log(S₄(τ)) = τ • (A + B) + τ⁵ • R₅(A, B, p) + τ⁷ • R₇(τ, A, B, p)
```

where `R₅` is a polynomial in 4-fold commutators of `A, B` with explicit
(bounded) prefactors under `IsSuzukiCubic p`, and `‖R₇‖ = O(τ²·…)`.

Differentiate in `τ`, compose with `exp_symmetric_bch_cubic`, and combine
with `norm_exp_add_sub_exp_le` + Lipschitz bounds to produce the pointwise
residual.

### Axiom 2: `bch_w4Deriv_level3_tight` (L3 — tight γᵢ)

```lean
axiom bch_w4Deriv_level3_tight
    (A B : 𝔸) (hA : star A = -A) (hB : star B = -B)
    (t : ℝ) (ht : 0 ≤ t) :
    let p : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))
    ∀ τ ∈ Set.Icc (0 : ℝ) t,
      ‖w4Deriv A B p τ‖ ≤ (5 * bchTightPrefactors.boundSum A B) * τ ^ 4
```

where `bchTightPrefactors : BCHPrefactors` holds eight explicit rational
coefficients γ₁…γ₈ obtained from the exact BCH R₅ projection at the Suzuki
root `p = 1/(4 - 4^(1/3))`. `boundSum A B = Σᵢ γᵢ · ‖Cᵢ‖`.

**Mathematical content.** Instead of unit coefficients, project R₅ onto the
8-Childs-commutator basis and extract the **numerically tight** γᵢ (each
strictly smaller than Childs's αᵢ; verified by
`bchTightPrefactors_le_childs`).

**Closure path.** After closing axiom 1, specialize to
`p = 1/(4 - 4^(1/3))`, perform the CAS-certified Childs-basis projection,
and get sharp γᵢ. The tight values are already available in Lean-Trotter
(`bchTightPrefactors` def in `Suzuki4ViaBCH.lean`); you only need to prove
the inequality, not discover the coefficients.

**Note.** Axiom 2 also underwrites the Childs-bound reproduction
`norm_suzuki4_childs_form_via_level3` via
`bchTightPrefactors_le_childs` (termwise γᵢ ≤ αᵢ, already Lean-proved).

### Axiom 3: `bch_uniform_integrated` (L4 — finite-t with R₇)

```lean
axiom bch_uniform_integrated
    (A B : 𝔸) (hA : star A = -A) (hB : star B = -B) {t : ℝ} (ht : 0 ≤ t) :
    let p : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))
    ‖suzuki4Exp A B p t - exp (t • (A + B))‖ ≤
      t ^ 5 * bchTightPrefactors.boundSum A B + t ^ 7 * bchR7Bound A B
```

where `bchR7Bound A B = bchR7UniformConstant · max ‖A‖ ‖B‖ ^ 7` and
`bchR7UniformConstant` is a fixed positive rational (from CAS computation
over 126 non-zero 7-letter words).

**Mathematical content.** This is the *integrated* (not pointwise) bound
with an explicit R₇ correction — valid for all `t ≥ 0`, not just asymptotic.

**Closure path (largest piece).** Extend Lean-BCH to **order-7 BCH
expansion** of the 5-factor palindromic product:
1. Symbolic computation of `log(S₄(τ))` to order τ⁷ (palindromic + Suzuki
   cubic makes orders 2, 3, 4, 6 vanish).
2. R₇ = degree-7 part, bounded by K · max(‖A‖, ‖B‖)^7 via triangle
   inequality on the 126 non-zero 7-letter words.
3. Integrate via FTC-2 (analogous to Lean-Trotter's Module 3,
   `norm_suzuki4_order5_via_module3`) with the pointwise bound
   `‖w4Deriv τ‖ ≤ (5 · tightSum) · τ⁴ + K · max(‖A‖,‖B‖)⁷ · (7 · τ⁶)`.

CAS scaffold exists in `scripts/compute_bch_r7.py` on the Lean-Trotter
side — you can reuse the numerical data.

## What Lean-Trotter will do once Lean-BCH extends

For each new Lean-BCH theorem, Lean-Trotter will

1. Bump the `lean-bch` rev in `lakefile.lean`.
2. Replace the corresponding `axiom bch_w4Deriv_*` with a short derivation
   (~20-40 lines each) that imports the Lean-BCH theorem and wires it
   through `norm_suzuki4_order5_via_module3` (Lean-Trotter's existing FTC-2
   reduction, signature below).

```lean
theorem norm_suzuki4_order5_via_module3 (A B : 𝔸)
    (hA : star A = -A) (hB : star B = -B) (p : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hCont : Continuous (w4Deriv A B p))
    {C : ℝ} (hC : 0 ≤ C)
    (hBound : ∀ τ ∈ Set.Icc (0 : ℝ) t, ‖w4Deriv A B p τ‖ ≤ C * τ ^ 4) :
    ‖suzuki4Exp A B p t - exp (t • (A + B))‖ ≤ C / 5 * t ^ 5
```

So the Lean-BCH API you expose should give the `hBound` ingredient directly
(or an ingredient that chains to it through a few lines of triangle
inequalities).

## Recommended order of attack

1. **Prove the 5-factor palindromic quintic remainder first.** This is the
   biggest new piece of Lean-BCH machinery. Once done, axiom 1 becomes a
   corollary. Call it something like
   `BCH.norm_suzuki5_palindromic_quintic_remainder`:
   ```
   ‖log(suzuki5Product A B p τ) - τ•(A+B) - τ⁵•R₅(A,B,p)‖ ≤ K(p) · τ⁶ · (‖A‖+‖B‖)⁶
   ```
   with `R₅` defined explicitly as a polynomial in 4-fold commutators.
   Model after Lean-BCH's existing
   `norm_symmetric_bch_cubic_sub_smul_le` (2-factor case) but for the
   5-factor palindromic expansion.

2. **Axiom 1 closure:** differentiate the quintic remainder formula in τ,
   bound each 4-fold commutator by the Childs-basis triangle inequality
   with unit coefficients, get the `5 · bchFourFoldSum` pointwise bound.

3. **Axiom 2 closure:** specialize step 1 to `p = 1/(4 - 4^(1/3))`, use the
   Childs-basis projection. The Lean-Trotter-side `bchTightPrefactors` def
   is frozen rational numbers — you prove that R₅ specialized to Suzuki `p`
   equals this combination exactly (or bounds by it termwise).

4. **Axiom 3 closure:** extend quintic remainder to order-7 expansion;
   integrate via FTC-2. This is the most work — CAS-assisted, ~200-500
   lines of careful polynomial arithmetic.

## Acceptance criteria

For each axiom closed:

- [ ] Lean-BCH `lake build` passes with no new sorries.
- [ ] A named theorem in `BCH/Palindromic.lean` (or a new module) provides
  the exact statement Lean-Trotter needs as a hypothesis for
  `norm_suzuki4_order5_via_module3`.
- [ ] Opacity: wrap any large polynomial expression as a
  `noncomputable def` (as in the existing `suzuki5_bch_M4b_RHS` pattern) to
  avoid whnf / isDefEq kernel timeouts when downstream proofs bound terms.
- [ ] Add a corollary that exactly matches the axiom signature Lean-Trotter
  expects (modulo renaming). Include the axiom signatures in a
  `/-! ### Lean-Trotter compatibility -/` section docstring.

## Definitions to reuse

From Lean-Trotter (look up in `LieTrotter/Suzuki4ChildsForm.lean` and
`LieTrotter/Suzuki4ViaBCH.lean`):
- `childsComm₁ A B … childsComm₈ A B` (the 8 four-fold commutators).
- `bchFourFoldSum A B = Σ ‖childsCommᵢ A B‖`.
- `BCHPrefactors` structure with 8 rational γᵢ fields.
- `bchTightPrefactors`, `childsPrefactors` (instances).
- `BCHPrefactors.boundSum p A B = Σᵢ p.γᵢ · ‖childsCommᵢ A B‖`.
- `bchR7Bound A B = bchR7UniformConstant · max ‖A‖ ‖B‖ ^ 7`.

You may duplicate these definitions on the Lean-BCH side (add them in a
new module `BCH/ChildsBasis.lean` or similar) so the axiom signatures can
be restated as Lean-BCH theorems. Lean-Trotter's definitions will then be
`rfl`-compatible thin wrappers.

## Scope

Do not touch Lean-Trotter. All changes are in the Lean-BCH repo. After
each axiom closure, post the new rev; Lean-Trotter will bump the pin and
flip the axiom to a theorem.

## Reference: Lean-BCH rev history

- `c71d8f2` (current Lean-Trotter pin): 0-sorries, opaque M4b RHS + M6
  Trotter-h4 bound, 2-factor quintic remainder.
- `fffca6c`: introduced opaque `suzuki5_bch_M4b_RHS` def (template for
  opacity when kernel timeouts threaten).
- `4ea6357`: payoff corollary `suzuki5_bch_M4b_RHS_le_t5_of_IsSuzukiCubic`
  (closed at `c71d8f2`).

Use the opacity + body-extraction pattern described in the Lean-BCH
`CLAUDE.md` "lessons" section for any sub-proofs that risk blowing up
kernel whnf heartbeats.

## Deliverable

A branch (or PR) on `Jue-Xu/Lean-BCH` that:
1. Adds theorems matching each of the three Lean-Trotter axiom signatures.
2. Passes `lake build` with zero sorries.
3. Includes a short `CLAUDE.md` update listing the new theorems and the
   rev at which each axiom becomes closeable on the Lean-Trotter side.

After each phase (axiom 1, then 2, then 3), push a commit and report the
rev so Lean-Trotter can integrate incrementally.
