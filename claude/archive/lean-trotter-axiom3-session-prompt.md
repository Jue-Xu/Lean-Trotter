# Lean-Trotter next session — discharge axiom 3 (`bch_uniform_integrated`)

## Context

After session-12 work on Lean-BCH and the subsequent pin bump on
Lean-Trotter `main` (commit `680df35`, pinning Lean-BCH at rev
`309ddef`), the Lean-Trotter axiom landscape is now:

```
#print axioms bch_w4Deriv_quintic_level2
  -- {propext, Classical.choice, Quot.sound,
  --  BCH.symmetric_bch_quintic_sub_poly_axiom}     -- Lean-BCH B1.c only

#print axioms bch_w4Deriv_level3_tight
  -- {propext, Classical.choice, Quot.sound,
  --  BCH.symmetric_bch_quintic_sub_poly_axiom}     -- same

#print axioms norm_suzuki4_level4_uniform
  -- {propext, Classical.choice, Quot.sound,
  --  bch_uniform_integrated}                       -- ★ this session ★
```

**Axiom 1 (`bch_w4Deriv_quintic_level2`)**: discharged (Lean-Trotter
rev `5a2c03e`). Now invokes `BCH.suzuki5_log_product_quintic_of_IsSuzukiCubic`.
**Axiom 2 (`bch_w4Deriv_level3_tight`)**: discharged (Lean-Trotter rev
`705791a`). Now invokes
`BCH.suzuki5_log_product_quintic_tight_at_suzukiP`.
**Axiom 3 (`bch_uniform_integrated`)**: **OPEN** — this session's target.

`bch_uniform_integrated` lives in
`LieTrotter/Suzuki4ViaBCH.lean:1072` and is the only remaining
theorem-level `axiom` in Lean-Trotter:

```lean
axiom bch_uniform_integrated
    (A B : 𝔸) (hA : star A = -A) (hB : star B = -B) {t : ℝ} (ht : 0 ≤ t) :
    let p : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))
    ‖suzuki4Exp A B p t - exp (t • (A + B))‖ ≤
      t ^ 5 * bchTightPrefactors.boundSum A B + t ^ 7 * bchR7Bound A B
```

(`bchR7Bound A B := bchR7UniformConstant * max ‖A‖ ‖B‖ ^ 7`,
`bchR7UniformConstant := 0.01951`, the CAS-computed Σ_w |coef(w)| over
all 7-letter R₇ words at Suzuki `p`.)

The downstream consumer `norm_suzuki4_level4_uniform` is a one-liner
that just unwraps the axiom. Removing the axiom converts it to a
fully-derived theorem, leaving Lean-Trotter dependent only on Lean's
standard 3 + Lean-BCH's `symmetric_bch_quintic_sub_poly_axiom` (B1.c).

## State at start of this session

- Lean-Trotter `main` @ `680df35`. Pin bump pushed (assuming you have
  pushed it; if not, push first via `git push origin main` or open a
  PR — the bump itself is just a one-line lakefile change).
- Lean-BCH `main` @ `309ddef`. Repository `0` sorries, `1` private
  axiom (`BCH.symmetric_bch_quintic_sub_poly_axiom` = B1.c) + Lean's
  3 standard.
- Lean-BCH **does not yet provide a τ⁷ identification theorem** (only
  τ⁶ — see `BCH.norm_suzuki5_bch_sub_smul_sub_R5_le`). This is a
  prerequisite this session must either build or stub.
- CAS R₇ data computed by `scripts/compute_bch_r7.py` — value
  `K ≈ 0.019509` already encoded as `bchR7UniformConstant = 0.01951`.

## Goal of this session

**Convert `bch_uniform_integrated` from axiom to theorem.** Two
sub-strategies are available; pick one based on appetite:

### Strategy A — full discharge (~2-4 weeks of Lean work)

End-to-end derivation analogous to Modules 2–3's FTC-2 pattern, lifted
one order higher:

1. **Lean-BCH-side τ⁷ identification** (~1500-2000 lines, the bulk of
   the work): extend
   `BCH.norm_suzuki5_bch_sub_smul_sub_R5_le` to identify the τ⁷
   residue as `τ⁷ • R₇ A B p` for an explicit `R₇ : 𝔸` (analog of
   `suzuki5_R5`), and bound the τ⁸ tail polynomially. Requires:
   - **Sextic BCH remainder** in `BCH/Basic.lean`: extend
     `bch_quartic_term` / `norm_bch_quintic_remainder_le` by one
     degree (mirrors what B1.c Tier-1 work would do for the symmetric
     BCH).
   - **R₇ Childs-basis identification**: the order-7 free Lie algebra
     has a basis of 18 elements (vs. 8 at order 5). The βᵢ₍₇₎(p)
     polynomial prefactors are computed by extending
     `scripts/compute_bch_prefactors.py` to `max_degree=7`.
   - **R₇ unit-coefficient norm bound**: `‖R₇ A B p‖ ≤
     bchR7UniformConstant * max ‖A‖ ‖B‖ ^ 7` derived from the βᵢ₍₇₎(p)
     polynomials at `p = suzukiP`. Replaces the Σ-of-absolute-value
     CAS computation with a Lean-side bound.
   - **τ⁸ tail bound**: existential `∃ δ K, ∀ τ < δ, ‖resid‖ ≤ K·τ⁸`
     analog of the τ⁶ tail in `norm_suzuki5_bch_sub_smul_sub_R5_le`.

2. **Lean-Trotter-side FTC-2 lift to integrated bound** (~300-500
   lines): the integrated bound from a pointwise level-3-tight + R₇
   bound on `w4Deriv`. Strategy mirrors `Suzuki4Module3.lean`'s
   `norm_w4_sub_one_le_t5_via_residual` (proved at order 5 via
   `intervalIntegral.integral_eq_sub_of_hasDerivAt` +
   `norm_integral_le_of_norm_le` + `integral_pow`):
   - Pointwise τ⁴ + τ⁶ bound on `‖w4Deriv A B p τ‖` by combining the
     Lean-BCH τ⁷ identification (level-3-tight γᵢ + R₇ K·max‖.‖⁷) with
     the existing `norm_suzuki4_diff_eq_norm_relative` bridge.
   - FTC-2 + `integral_pow` for τ⁴ → τ⁵/5 and τ⁶ → τ⁷/7.
   - Combine to `‖S₄(t) - exp(tH)‖ ≤ t⁵·boundSum + t⁷·bchR7Bound`.

3. **Delete the axiom + verify**:
   ```
   #print axioms norm_suzuki4_level4_uniform
   -- expect: {propext, Classical.choice, Quot.sound,
   --          BCH.symmetric_bch_quintic_sub_poly_axiom}
   ```

### Strategy B — partial discharge (~3-5 days, more pragmatic)

Decompose `bch_uniform_integrated` into smaller pieces, axiomatize the
genuinely new ones, and discharge the Lean-Trotter-side composition:

1. **Axiomatize a Lean-BCH-side τ⁷ identification** as a single new
   `private axiom` in `BCH/Suzuki5Quintic.lean`:
   ```
   axiom suzuki5_R5_R7_identification :
     ∃ K ≥ 0, ∀ τ : ℝ, ‖τ‖ ≤ 1 →
       ‖suzuki5_bch ℝ A B suzukiP τ - τ • (A + B) -
        τ ^ 5 • suzuki5_R5 A B suzukiP - τ ^ 7 • R7 A B‖ ≤ K * ‖τ‖ ^ 8
   ```
   (with `R7 : 𝔸 → 𝔸 → 𝔸` an explicit Childs-basis-style def whose
   norm bound `‖R7 A B‖ ≤ bchR7UniformConstant·max‖A‖‖B‖^7` is also
   asserted as a small companion axiom or proved directly from
   βᵢ₍₇₎(suzukiP) ≤ rationals).
2. **FTC-2 lift on Lean-Trotter side** (~300-500 lines): same as
   Strategy A's step 2 above. This part has no new axiom dependencies
   — it's pure analysis.
3. **Discharge `bch_uniform_integrated` from the new Lean-BCH axiom +
   FTC-2 lemma**: short composition.

This trades one axiom (`bch_uniform_integrated`) for one new axiom
(`suzuki5_R5_R7_identification`) but **moves the burden to the right
place** (the symbolic τ⁷ identification belongs in Lean-BCH; the FTC-2
integration belongs in Lean-Trotter), and produces actual
Lean-Trotter-side analysis content. Future sessions can then discharge
the new Lean-BCH axiom independently, mirroring the P1 → discharge
arc.

## Recommended path

**Strategy B**, then schedule Strategy A's step 1 as a follow-up Lean-BCH
session. Rationale:
- Strategy A's step 1 alone is a ~2-3 week Lean-BCH project (R₇
  Childs basis, βᵢ₍₇₎ polynomials, sextic BCH remainder, full
  identification). Doing it inline with the FTC-2 lift mixes
  unrelated work and risks running up token / patience budget.
- Strategy B produces a useful intermediate result: a fully proved
  FTC-2 lift theorem on the Lean-Trotter side, which is independently
  usable and verifiable.
- The new Lean-BCH axiom in Strategy B has the same structural shape
  as the discharged P1 axiom — its discharge can follow the same
  template (regime helpers, decomposition, per-term bounds, le_trans
  assembly) one degree higher.

## Files to modify

### Lean-Trotter (this session, Strategy B)

- `LieTrotter/Suzuki4ViaBCH.lean`: replace the `axiom
  bch_uniform_integrated` body with `theorem bch_uniform_integrated
  ... := by ...`. Compose the new Lean-BCH axiom with an FTC-2 lift.
- (Possibly new file) `LieTrotter/Suzuki4Module4Uniform.lean` or
  similar for the FTC-2 lift, to keep `Suzuki4ViaBCH.lean`
  focused on the BCH composition.
- `claude/`: add a Strategy A follow-up prompt for the eventual full
  discharge (mirrors the lean-bch-B1c-session-prompt.md style).

### Lean-BCH (this session, Strategy B)

- `BCH/Suzuki5Quintic.lean`: add `private axiom
  suzuki5_R5_R7_identification` + its definitional companions (`R7`
  def, R7 norm bound). Update `CLAUDE.md` "Remaining axioms" section
  to document the new axiom and its discharge roadmap.
- `lakefile.lean` or release notes: bump after merging.

### Coordinated bump

- After Lean-BCH adds the new axiom + R7 def + R7 norm bound, push to
  origin/main. Then bump Lean-Trotter pin to the new SHA, rebuild, and
  verify `#print axioms` reports `bch_uniform_integrated` depends on
  the new Lean-BCH axiom (and only it).

## Reference: similar templates

- **FTC-2 reduction at order 5**: `Suzuki4Module3.lean`'s
  `norm_w4_sub_one_le_t5_via_residual` (line ~58). Same pattern,
  with `t ^ 4` → `t ^ 4 + K · t ^ 6` in the pointwise bound and the
  integration producing `t ^ 5 / 5 + K · t ^ 7 / 7`.
- **R₇ data**: `scripts/compute_bch_r7.py` produces
  `K ≈ 0.019509` and the per-word coefficients. The encoded value
  `bchR7UniformConstant = 0.01951` already covers it with safety
  margin (verified by `bchR7UniformConstant_covers_cas` lemma at
  line ~1025).
- **Lean-BCH τ⁵ identification template** (for follow-up Strategy A
  step 1, to mirror at degree 7):
  - `BCH.suzuki5_R5` (in `BCH/Suzuki5Quintic.lean`) — the τ⁵
    Childs-basis combination.
  - `BCH.norm_suzuki5_bch_sub_smul_sub_R5_le` — the headline
    identification theorem (now fully proved, ~1100 lines).
  - `BCH.suzuki5_log_product_quintic_of_IsSuzukiCubic` — the bridge
    corollary.
  - `BCH.suzuki5_log_product_quintic_tight_at_suzukiP` — the tight
    bridge (consumed by Lean-Trotter axiom 2).

## Estimated effort (Strategy B)

- Lean-BCH new axiom + R7 def + R7 norm bound: ~200-300 lines.
- Lean-Trotter FTC-2 lift: ~300-500 lines.
- Pin bump + verification: trivial.
- Total: 3-5 days.

## Optional follow-up (out of scope)

- Discharge `BCH.symmetric_bch_quintic_sub_poly_axiom` (B1.c) on
  Lean-BCH side — Tier 1/2/3 roadmap in
  `BCH/SymmetricQuintic.lean` module header. ~2-3 weeks.
- Discharge `suzuki5_R5_R7_identification` on Lean-BCH side via the
  Strategy A step 1 template. ~2-4 weeks.
