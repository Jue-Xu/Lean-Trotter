# Prompt: Lean-BCH next session — discharge private axiom + infrastructure for axioms 2 & 3

## Context

This prompt continues the `trotter-5factor-palindromic` branch of Lean-BCH
(https://github.com/Jue-Xu/Lean-BCH). The branch's prior session added
τ⁵-identification infrastructure (βᵢ(p) polynomials, `suzuki5_R5` def,
unit-coefficient norm bound, headline theorem
`norm_suzuki5_bch_sub_smul_sub_R5_le`, and the bridge corollary
`suzuki5_log_product_quintic_of_IsSuzukiCubic`) — gated behind one scoped
private axiom `BCH.suzuki5_R5_identification_axiom`.

Downstream on Lean-Trotter (rev `5a2c03e` of
https://github.com/Jue-Xu/Lean-Trotter), the `bch_w4Deriv_quintic_level2`
axiom has now been converted to a theorem that invokes
`BCH.suzuki5_log_product_quintic_of_IsSuzukiCubic` directly. Axiom
inspection on the headline Lean-Trotter theorems shows:

    bch_w4Deriv_quintic_level2         : {propext, Classical.choice, Quot.sound,
                                           BCH.suzuki5_R5_identification_axiom}
    norm_suzuki4_level2_bch            : same
    bch_iteratedDeriv_s4Func_order4    : {propext, Classical.choice, Quot.sound}
    lie_trotter                        : same

So the only remaining `sorryAx`-adjacent dependency in Lean-Trotter's
Level-2 BCH bound is the Lean-BCH-side private axiom
`BCH.suzuki5_R5_identification_axiom`. Two other Lean-Trotter axioms
(`bch_w4Deriv_level3_tight`, `bch_uniform_integrated`) remain and need
fresh Lean-BCH infrastructure.

## Goals (prioritized)

### Priority 1: Discharge `BCH.suzuki5_R5_identification_axiom`

The axiom currently states (schematic): under `IsSuzukiCubic p`, there
exist δ > 0 and K ≥ 0 such that for all τ with ‖τ‖ < δ,

    ‖suzuki5_bch ℝ A B p τ − τ•(A+B) − τ⁵ • suzuki5_R5 A B p‖ ≤ K·‖τ‖⁶.

This is the **core Tier-2 symbolic result**: the 5-factor palindromic BCH
expansion identifies its τ⁵ coefficient with the explicit
Childs-basis combination `suzuki5_R5 A B p = Σᵢ βᵢ(p)·Cᵢ(A,B)`.

**Three-tier roadmap** (see `BCH/Suzuki5Quintic.lean` header):

- **Tier 1 (~1-2 days)**. Extend `Basic.lean`'s 2-factor
  `norm_symmetric_bch_cubic_sub_smul_le` to a quintic Taylor expansion of
  each `strangBlock_log A B c τ`:

        ∃ δ > 0, ∃ K ≥ 0, ∀ τ : ℝ, ‖τ‖ < δ →
          ‖strangBlock_log A B c τ − (c·τ)•(A+B) − (c·τ)³·E₃ − (c·τ)⁵·E₅‖
            ≤ K·‖c·τ‖⁶·(‖A‖+‖B‖)⁶

  where `E₃ = symmetric_bch_cubic` (existing) and `E₅` is the quintic
  BCH coefficient for the symmetric Strang block.

- **Tier 2 (~weeks, the hardest)**. Symbolic triple-BCH composition.
  Substitute Tier 1 into
  `suzuki5_bch = bch(bch(2X, Y), 2X)` where `X = strangBlock_log(p·τ)`
  and `Y = strangBlock_log((1-4p)·τ)`. Expand each `bch(U, V)` via
  `norm_bch_sub_add_sub_bracket_le` (H1), collect terms of order τ⁵,
  and perform the Gauss-Jordan projection onto the Childs 4-fold
  commutator basis. LCM of denominators ≈ 144000 at Suzuki p; use
  scalar-clearing `noncomm_ring` strategy (multiply both sides by LCM
  before calling `noncomm_ring`).

  The CAS-verified output is encoded in
  `Lean-Trotter/scripts/compute_bch_prefactors.py` (the 8 βᵢ(p)
  polynomials). Port each βᵢ coefficient-by-coefficient.

- **Tier 3 (~1 day)**. Triangle-inequality residual bounding. Combine
  the existing `suzuki5_bch_M4b_RHS_le_t5_of_IsSuzukiCubic`
  (rev `c71d8f2`) with the Tier 1 and Tier 2 residuals to close the
  `K·‖τ‖⁶` bound on the full identification.

Implementation notes:

- Preserve the **opacity** pattern: once a large polynomial expression is
  derived, wrap it as a `noncomputable def` (as in
  `suzuki5_bch_M4b_RHS`) to avoid whnf/isDefEq kernel timeouts
  downstream.
- Add a `private theorem suzuki5_R5_identification_tier2_closed` with
  the axiom's exact signature; then rewrite
  `norm_suzuki5_bch_sub_smul_sub_R5_le` to invoke the new theorem
  instead of the axiom. Remove the `private axiom` line.
- After removal, `#print axioms BCH.norm_suzuki5_bch_sub_smul_sub_R5_le`
  should return only `{propext, Classical.choice, Quot.sound}`.

### Priority 2: Infrastructure for Lean-Trotter axiom 2 (`bch_w4Deriv_level3_tight`)

Lean-Trotter's current axiom (in `LieTrotter/Suzuki4ViaBCH.lean`):

    axiom bch_w4Deriv_level3_tight
        (A B : 𝔸) (hA : star A = -A) (hB : star B = -B)
        (t : ℝ) (ht : 0 ≤ t) :
        let p : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))
        ∀ τ ∈ Set.Icc (0 : ℝ) t,
          ‖w4Deriv A B p τ‖ ≤ (5 * bchTightPrefactors.boundSum A B) * τ ^ 4

where `bchTightPrefactors : BCHPrefactors` holds 8 explicit rational
coefficients γᵢ (each strictly smaller than Childs's αᵢ) and
`boundSum A B = Σᵢ γᵢ · ‖Cᵢ(A, B)‖`.

**Following the signature-adjustment pattern from axiom 1**, propose a
matching Lean-BCH bridge corollary:

    theorem suzuki5_log_product_quintic_tight_at_suzukiP
        (A B : 𝔸) :
        let p : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))
        ∃ δ > (0 : ℝ), ∃ K ≥ (0 : ℝ), ∀ τ : ℝ, 0 ≤ τ → τ < δ →
          ‖suzuki5_bch ℝ A B p τ − τ • (A + B)‖ ≤
            τ ^ 5 * tightPrefactorsBoundSum A B + K * τ ^ 6

where `tightPrefactorsBoundSum A B = Σᵢ γᵢ · ‖childsCommᵢ A B‖`.

**Closure path in Lean-BCH:**
1. Port `BCHPrefactors` and `bchTightPrefactors` from Lean-Trotter's
   `Suzuki4ViaBCH.lean` to a new Lean-BCH module
   `BCH/ChildsBasisPrefactors.lean` (or extend `ChildsBasis.lean`).
2. Define `tightPrefactorsBoundSum` as the Childs-basis combination
   `Σᵢ γᵢ · ‖Cᵢ A B‖`.
3. Specialize the τ⁵ identification (from Priority 1) to Suzuki p:
   substitute the 8 βᵢ(Suzuki p) values — each provably ≤ γᵢ — into
   the R₅ sum. Prove
   `‖suzuki5_R5 A B (suzukiP)‖ ≤ tightPrefactorsBoundSum A B`.
4. Combine with triangle inequality as in
   `suzuki5_log_product_quintic_of_IsSuzukiCubic`.
5. Downstream on Lean-Trotter: rewrite `bch_w4Deriv_level3_tight`
   axiom to theorem matching this signature, and rewrite
   `norm_suzuki4_level3_bch` (analogous to the axiom 1 rewrite).

### Priority 3: Infrastructure for Lean-Trotter axiom 3 (`bch_uniform_integrated`)

Lean-Trotter's current axiom:

    axiom bch_uniform_integrated
        (A B : 𝔸) (hA : star A = -A) (hB : star B = -B) {t : ℝ} (ht : 0 ≤ t) :
        let p : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))
        ‖suzuki4Exp A B p t - exp (t • (A + B))‖ ≤
          t ^ 5 * bchTightPrefactors.boundSum A B + t ^ 7 * bchR7Bound A B

where `bchR7Bound A B = bchR7UniformConstant · max ‖A‖ ‖B‖ ^ 7` and
`bchR7UniformConstant ≈ 0.01951`.

**This is the biggest remaining piece** — requires **order-7 BCH expansion
of the 5-factor palindromic product** (palindromic + Suzuki cubic makes
orders 2, 3, 4, 6 vanish; extract R₇ as the degree-7 residual).

**Closure path:**
1. Extend Tier-1 quintic Taylor expansion of `strangBlock_log` to order
   τ⁷ (one more order).
2. Substitute into Tier-2 triple-BCH composition at order τ⁷; collect
   126 non-zero 7-letter word monomials; project onto an appropriate
   basis.
3. Prove `‖R₇(A, B, suzukiP)‖ ≤ K · max(‖A‖, ‖B‖)^7` via triangle
   inequality (the CAS computation in
   `Lean-Trotter/scripts/compute_bch_r7.py` gives K ≈ 0.01951 but K
   can be an over-approximation).
4. Bridge corollary:

        theorem suzuki5_log_product_septic_at_suzukiP
            (A B : 𝔸) {t : ℝ} (ht : 0 ≤ t) :
            let p : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))
            ‖suzuki5_bch ℝ A B p t − t • (A + B)‖ ≤
              t ^ 5 * tightPrefactorsBoundSum A B + t ^ 7 * r7Bound A B

   — note this is a *uniform* finite-t bound, not an existential one:
   the τ⁷ term absorbs the higher-order tail.

5. Downstream on Lean-Trotter: convert the axiom to theorem;
   `norm_suzuki4_level4_uniform` gets the exp-Lipschitz composition
   treatment as in the axiom 1 rewrite.

## Setup

```bash
# Work on the same branch
cd ~/Documents/Lean-BCH   # or wherever the Lean-BCH clone lives
git checkout trotter-5factor-palindromic
git pull
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get
lake build                # baseline build before any code changes
```

Lean-Trotter's current pin is `7ba3962` (pre-this-session). After this
session lands new commits, Lean-Trotter will bump the pin.

## Acceptance criteria

### For Priority 1

- [ ] `BCH.suzuki5_R5_identification_axiom` is removed from
      `BCH/Suzuki5Quintic.lean`; replaced by a `private theorem`
      with the same signature.
- [ ] `#print axioms BCH.norm_suzuki5_bch_sub_smul_sub_R5_le` returns
      only `{propext, Classical.choice, Quot.sound}`.
- [ ] `#print axioms BCH.suzuki5_log_product_quintic_of_IsSuzukiCubic`
      same.
- [ ] `lake build` passes with zero sorries (keep the existing
      `grep sorry BCH/*.lean` → 0 invariant).
- [ ] CLAUDE.md status section updated.
- [ ] Pushed commit reported so Lean-Trotter can bump the pin and
      rerun `#print axioms bch_w4Deriv_quintic_level2` — expected
      closure after bump: `{propext, Classical.choice, Quot.sound}`
      (no more `BCH.suzuki5_R5_identification_axiom`).

### For Priority 2

- [ ] `BCH.ChildsBasisPrefactors` (or extended `ChildsBasis`) module
      with `BCHPrefactors` structure + `bchTightPrefactors` instance
      (values copied from Lean-Trotter's `bchTightPrefactors`).
- [ ] `BCH.tightPrefactorsBoundSum A B` definition.
- [ ] Theorem
      `BCH.suzuki5_log_product_quintic_tight_at_suzukiP` with
      signature as proposed above, proved (depends on Priority 1
      being closed; otherwise chain through the private axiom).
- [ ] `lake build` passes.
- [ ] CLAUDE.md updated with the new theorem.

### For Priority 3

- [ ] Order-7 BCH machinery (Tier 1 extended to τ⁷;
      `suzuki5_R7 A B p` opaque def; `norm_suzuki5_R7_le_r7Bound`).
- [ ] Bridge theorem `BCH.suzuki5_log_product_septic_at_suzukiP` per
      the signature above.
- [ ] `lake build` passes.
- [ ] CLAUDE.md updated.

## Coordination with Lean-Trotter

After each priority closes, post the new Lean-BCH rev; Lean-Trotter
will:

- Priority 1: bump the pin, and `#print axioms bch_w4Deriv_quintic_level2`
  will show only `{propext, Classical.choice, Quot.sound}` (no more
  `BCH.suzuki5_R5_identification_axiom`). Victory condition for axiom 1.
- Priority 2: convert `bch_w4Deriv_level3_tight` to a theorem in
  `LieTrotter/Suzuki4ViaBCH.lean` (pattern follows
  `bch_w4Deriv_quintic_level2`), and rewrite `norm_suzuki4_level3_bch`
  + `norm_suzuki4_childs_form_via_level3` with the
  existential-t shape.
- Priority 3: convert `bch_uniform_integrated` to a theorem; rewrite
  `norm_suzuki4_level4_uniform`.

Each Lean-Trotter-side conversion is expected to be a ~100-200 line
operation (proof + doc updates + axiom inspection), similar in scope
to the axiom-1 conversion already landed at Lean-Trotter rev `5a2c03e`.

## Background: axiom 1 closure on the Lean-Trotter side

For reference, the Lean-Trotter-side pattern that worked for axiom 1
(can be replicated for axioms 2 and 3):

1. Change axiom to theorem with signature matching Lean-BCH's bridge
   (∃ δ > 0, ∃ K ≥ 0, ∀ τ ∈ [0, δ), ‖log-bound‖ ≤ τ⁵·Σ + K·τ⁶).
2. Proof body = one-liner citing the Lean-BCH bridge.
3. Rewrite the downstream Trotter theorem (`norm_suzuki4_level*_bch`)
   to give an existential-t `∃ δ > 0, ∃ C ≥ 0, ∀ τ, 0 ≤ τ → τ < δ →
   ‖S₄(τ) - exp(τ•H)‖ ≤ C·τ⁵` bound, proved via:
   - the new theorem (log bound),
   - `BCH.exp_suzuki5_bch` (M2b round-trip: `S₄ = exp(suzuki5_bch)`),
   - `BCH.norm_exp_add_sub_exp_le` (exp-Lipschitz),
   - `τ⁶ ≤ τ⁵` for `τ ∈ [0, 1]` (after shrinking δ to min(δ_BCH, 1)).
4. Axiom inspection confirms `{propext, Classical.choice, Quot.sound,
   BCH.<remaining_private_axiom>}` (or fewer once Priority 1 lands).

See Lean-Trotter commit `5a2c03e` for a concrete reference
implementation.

## Out of scope

- Mathlib contributions (the general-purpose Banach-algebra exp
  bounds in `BCH/Basic.lean` could be upstreamed eventually, but not
  this session).
- Total-error convergence theorems on the Lean-Trotter side.
- Minimum-ℓ¹ Childs projection refinement.

## References

- **Lean-Trotter current HEAD**: `5a2c03e` on `main`
  (https://github.com/Jue-Xu/Lean-Trotter).
- **Lean-BCH branch HEAD**: `7ba3962` on `trotter-5factor-palindromic`
  (https://github.com/Jue-Xu/Lean-BCH).
- **Pre-existing CAS script**:
  `Lean-Trotter/scripts/compute_bch_prefactors.py` — 8 βᵢ(p) polynomials
  (closed forms) + γᵢ = βᵢ(Suzuki p) numerical values.
- **R₇ CAS script**: `Lean-Trotter/scripts/compute_bch_r7.py` — K ≈
  0.01951 uniform constant.
- **Reference paper**: Childs et al.,
  "Theory of Trotter Error with Commutator Scaling", PRX 11, 011020 (2021).

## Estimated total time

- Priority 1: 1-3 weeks (Tier 2 symbolic work is the bottleneck).
- Priority 2: 2-5 days (assumes Priority 1 is closed; mostly
  specialization + Childs-basis projection).
- Priority 3: 1-2 weeks (order-7 extension; uniform bound with R₇;
  numeric specialization).

Recommend tackling in order; each priority unlocks the next on the
Lean-Trotter side, and each corresponds to a clean Lean-Trotter-side
axiom-to-theorem conversion session.
