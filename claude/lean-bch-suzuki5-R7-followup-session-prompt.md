# Lean-BCH next session — discharge `suzuki5_log_product_septic_at_suzukiP_axiom`

## Context

Session N (2026-04-26) added a new private axiom in
`BCH/Suzuki5Quintic.lean` (commit `cf5eea3` on `main`):

```lean
private axiom suzuki5_log_product_septic_at_suzukiP_axiom (A B : 𝔸) :
    ∃ δ > (0 : ℝ), ∃ M ≥ (0 : ℝ), ∀ τ : ℝ, 0 ≤ τ → τ < δ →
      ‖suzuki5_bch ℝ A B suzukiP τ - τ • (A + B)‖ ≤
        τ ^ 5 * bchTightPrefactors.boundSum A B +
        τ ^ 7 * bchR7Bound A B +
        M * τ ^ 8
```

(`bchR7Bound A B := bchR7UniformConstant * max ‖A‖ ‖B‖^7`,
`bchR7UniformConstant := 0.01951`, the rational ceiling for the
CAS-computed `K ≈ 0.019509` from
`Lean-Trotter/scripts/compute_bch_r7.py`.)

This is the τ⁷ identification analog of the (now-discharged) P1 axiom
`suzuki5_R5_identification_axiom`. It extends the τ⁵ identification by one
order: identifies the τ⁷ leading content of `suzuki5_bch` with the
explicit Childs-7-basis projection R₇, with `O(τ⁸)` tail.

## State at start of this session

- Lean-BCH `main` @ `cf5eea3` (or later): the new axiom + bridge
  `suzuki5_log_product_septic_at_suzukiP` are in place.
- Lean-Trotter `main` @ ??? (pin bumped to `cf5eea3` after session N+1):
  `bch_uniform_integrated` is now a theorem (not an axiom), depending
  only on Lean's 3 standard + the new BCH axiom.
- Discharged Lean-BCH axioms (3 + B1.c remaining): see
  `BCH/CLAUDE.md` "Remaining axioms" section.

## Goal of this session

**Convert `suzuki5_log_product_septic_at_suzukiP_axiom` from axiom to
theorem.** This requires extending the existing P1-discharge chain
(session 12) by one more BCH order.

### Required new infrastructure (sketched in order of dependency)

#### 1. Sextic BCH remainder (in `BCH/Basic.lean`)

Extend `bch_quartic_term` and `norm_bch_quintic_remainder_le` by one
degree:

- `bch_quintic_term a b : 𝔸` — the explicit degree-5 coefficient of
  `bch(a, b)`, expressible as a sum of degree-5 nested commutator
  monomials (Childs basis: 6 elements — see `BCH/ChildsBasis.lean`).
- `norm_bch_sextic_remainder_le` — `‖bch a b - (a + b) - 𝒸𝒶 - 𝓆𝒸 - 𝓆𝒹‖ ≤ K · s⁶`
  (where 𝒸𝒶 = `[a,b]/2`, 𝓆𝒸 = `bch_quartic_term`, 𝓆𝒹 = `bch_quintic_term`).

The proof parallels `norm_bch_quintic_remainder_le` (~800 lines at line
2326 of `Basic.lean`). Estimated ~500 lines.

#### 2. Symmetric BCH septic remainder

Apply the BCH expansion to the 3-factor `bch(bch(a/2, b), a/2)`
construction:

- `symmetric_bch_septic_poly` — the explicit degree-7 polynomial part.
- `norm_symmetric_bch_septic_sub_poly_le` — `‖sym_bch a b - sym_cubic_poly - sym_quintic_poly - sym_septic_poly‖ ≤ K · (‖a‖+‖b‖)^8`.

This depends on the new sextic remainder (#1). Estimated ~600 lines
(parallels the existing `norm_symmetric_bch_quintic_sub_poly_le` /
`norm_symmetric_bch_cubic_sub_poly_le` template).

#### 3. R₇ definition (in `BCH/Suzuki5Quintic.lean`)

Add:
- `suzuki5_β₁₍₇₎ … suzuki5_β_N₍₇₎` — the polynomial-in-`p` coefficients
  for the Childs-7-basis projection of R₇. These are computed by
  extending `Lean-Trotter/scripts/compute_bch_prefactors.py` to
  `max_degree=7`.
- `suzuki5_R7 : 𝔸 → 𝔸 → ℝ → 𝔸` — the explicit `Σᵢ βᵢ₍₇₎(p) · Cᵢ⁽⁷⁾`
  combination on the Childs-7 basis (or whichever basis the CAS chooses).
- `norm_suzuki5_R7_at_suzukiP_le_bchR7Bound` — at `p = suzukiP`,
  `‖suzuki5_R7 A B suzukiP‖ ≤ bchR7Bound A B`. Proved via
  `nlinarith` on per-i numerical bounds + triangle inequality (~100
  lines, parallels `norm_suzuki5_R5_at_suzukiP_le_bchTightPrefactors_boundSum`).

#### 4. Algebraic decomposition (B-type identity)

`suzuki5_bch_sub_R5_R7_decomp_at_suzukiP` — algebraic backbone splitting
`suzuki5_bch − τ•V − τ⁵•R₅ − τ⁷•R₇` into explicit summands, each
bounded by `O(τ⁸)`. Mirrors `suzuki5_bch_sub_R5_decomp_of_IsSuzukiCubic`
(B2.5 backbone for the τ⁵ identification).

#### 5. Per-summand bounds + regime helpers + assembly

Following the P1 discharge template (session 12, ~1100 lines):
- ~6 regime helpers from `‖τ‖ < 1/(10^N · pn · qn · s)` for some N
  (likely `N ≥ 13` to handle the higher-order corrections).
- Per-summand `O(τ⁸)` bounds (~7 helpers, similar structure to T1, T2a/b/c, T3).
- `under_regime` assembly via `suzuki5_bch_sub_R5_R7_decomp` + triangle
  inequality.
- Public theorem closing the existential-δ form, mirroring
  `norm_suzuki5_bch_sub_smul_sub_R5_le`.

Estimated total: ~2000-2500 lines.

#### 6. Convert axiom → theorem

Replace the `private axiom` with `private theorem` body:

```lean
private theorem suzuki5_log_product_septic_at_suzukiP_axiom (A B : 𝔸) :
    ∃ δ > (0 : ℝ), ∃ M ≥ (0 : ℝ), ∀ τ : ℝ, 0 ≤ τ → τ < δ →
      ‖suzuki5_bch ℝ A B suzukiP τ - τ • (A + B)‖ ≤
        τ ^ 5 * bchTightPrefactors.boundSum A B +
        τ ^ 7 * bchR7Bound A B +
        M * τ ^ 8 := by
  -- Compose the τ⁷-identification (#5 above) with the per-i numerical
  -- bounds (#3) via the same triangle-inequality pattern as
  -- `suzuki5_log_product_quintic_tight_at_suzukiP`.
  ...
```

After discharge, `#print axioms suzuki5_log_product_septic_at_suzukiP`
should report only `[propext, Classical.choice, Quot.sound,
BCH.symmetric_bch_quintic_sub_poly_axiom]` (B1.c, the only remaining
project axiom).

## Estimated effort

- Sextic remainder (#1): ~1 week.
- Symmetric BCH septic remainder (#2): ~1.5 weeks.
- R₇ definition + numerical bounds (#3): ~2-3 days.
- Algebraic decomposition (#4): ~1 week.
- Per-summand bounds + assembly (#5): ~1 week.
- Wiring (#6): ~1 day.

**Total: ~4-5 weeks of focused Lean work.**

## Verification

After discharge:

```
#print axioms BCH.suzuki5_log_product_septic_at_suzukiP
-- Expected: {propext, Classical.choice, Quot.sound,
--            BCH.symmetric_bch_quintic_sub_poly_axiom}

#print axioms bch_uniform_integrated  -- in Lean-Trotter
-- Expected: same 4 axioms (no new dependencies)
```

## Reference templates

The existing P1 discharge (session 12, ~1100 lines added) is the
template. Files:

- `BCH/Suzuki5Quintic.lean` lines 1300-2750 — the full P1 discharge:
  - Regime helpers: lines 700-980.
  - Per-summand bounds: lines 990-2230.
  - Public theorem assembly: line 2280.
- `BCH/Basic.lean` line 2326 — the existing quintic-remainder proof
  (template for the sextic-remainder #1).
- `BCH/Palindromic.lean` — symmetric BCH cubic + quintic per-block
  bounds (template for septic per-block #2).

## Optional follow-up (out of scope)

- Discharge `BCH.symmetric_bch_quintic_sub_poly_axiom` (B1.c). See
  `claude/lean-bch-B1c-session-prompt.md` for the 3-tier roadmap.
  After both discharges, Lean-BCH would be axiom-free except for
  Lean's standard 3.
