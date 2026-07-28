# Changelog — Lie-Trotter Lean 4 Formalization

Lab notes: completed tasks, failed approaches, and key decisions.

---

## 2026-07-28: Lean-BCH septic dependency is project-axiom-free

**Author:** OpenAI Codex

**What:** Updated the Lean-BCH dependency from `d455ff0` to the verified
zero-project-axiom revision `05e8c52`. The direct Mathlib pin remains
`06a46dae`; `lake update lean-bch` resolved the full Lean-BCH commit
`05e8c52fdd3d75c4e0c0d3c32360bc4c11417bcf` without moving Mathlib.
The public septic bridge type is unchanged, so no Lean-Trotter proof body
needed modification. Comments in two source files were refreshed to remove
stale descriptions of the former upstream septic axioms.

**Verification:** On the 384-CPU, approximately 1.48-TiB server, the isolated
target build `lake build LieTrotter.Suzuki4ViaBCH` completed 3,371 jobs with
zero errors. Its first cache-populating run took about 6 h 11 min, including
the approximately 4 h 12 min `BCH.Suzuki5Quintic` elaboration. After syncing
the final comment-only source state and matching SHA-256 hashes, the exact
target rerun completed in about 14 seconds. A complete `lake build` then
completed 3,386 jobs with zero errors in about 38 seconds.

`#print axioms` reports exactly `propext`, `Classical.choice`, and
`Quot.sound` for all of:

- `BCH.suzuki5_log_product_septic_at_suzukiP`
- `norm_suzuki4_level3_bch`
- `norm_suzuki4_childs_form_via_level3`
- `bch_uniform_integrated`
- `norm_suzuki4_level4_uniform`

The source census finds no Lean-Trotter `axiom`, `sorry`, or `admit`
declaration.

**Scope:** This verifies the committed
`origin/s4-total-error-convergence` baseline at `c583524` plus the dependency
upgrade. The user's original Lean-Trotter checkout contains substantial
uncommitted Lean and manuscript work, including overlapping edits to
`Suzuki4ViaBCH.lean`; it was not modified. Preserve or commit that work before
reconciling this isolated integration branch.

**Signed:** OpenAI Codex

## 2026-07-14: S₄ total-error convergence — O(1/n⁴), axiom-free

**What:** New file `LieTrotter/Suzuki4Convergence.lean` (~230 lines,
0 sorries). Closes the last structural gap in the S₄ track: every other
integrator here had both a single-step error bound *and* a compounded
convergence theorem; S₄ had only the step bound.

**New results (all `[propext, Classical.choice, Quot.sound]` only):**

| Theorem | Statement |
|---|---|
| `norm_suzuki4Exp_le` | `‖S₄(τ)‖ ≤ exp(\|τ\|·s4Rate A B p)` |
| `suzuki4_total_error_quartic` | `‖S₄(t/n)ⁿ − exp(t(A+B))‖ ≤ C/n⁴` for `n ≥ N` |
| `suzuki4_convergence_quartic` | `S₄(t/n)ⁿ → exp(t(A+B))` |
| `suzuki4_product_formula` | unit-time form: `S₄(1/n)ⁿ → exp(A+B)` |
| `suzuki4_{convergence,total_error}_quartic_suzukiP` | same, at `p = 1/(4−4^{1/3})`, **no hypotheses** |
| `suzuki4Step_eq_suzuki4Exp` | bridge: `suzuki4Step ℝ A B p n = suzuki4Exp A B p (1/n)` |
| `suzuki4Step_total_error_quartic` | **O(1/n⁴) for `suzuki4Step`** — upgrades `suzuki4_error_rate_sq` |
| `suzuki4Step_convergence_quartic` | **O(1/n⁴) convergence for `suzuki4Step`** |

This completes the hierarchy `lie_trotter` (O(1/n)) → `symmetric_lie_trotter`
(O(1/n²)) → `suzuki4_convergence_quartic` (O(1/n⁴)).

**The `suzuki4Step` bridge.** `Suzuki4.lean` builds S₄ from five `strangStep`s
(each with a built-in `1/n`) and bounds it at O(1/n²) — the generic rate available
*without* the cubic condition. `suzuki4Exp` builds the same operator as 11
exponentials in a free step size `τ`. `suzuki4Step_eq_suzuki4Exp` identifies them,
so `suzuki4Step_{total_error,convergence}_quartic` restate the new results for the
*same* object, making the O(1/n²) → O(1/n⁴) improvement explicit rather than a
comparison across two definitions.

Cheaper than expected: `suzuki4Exp_eq_strangProduct` (Suzuki4StrangBlocks.lean)
already performs the four junction merges of adjacent same-operator exponentials,
so the bridge reduces to the scalar identity `strangStep(c,n) = strangBlock(c/n)`
(`strangStep_eq_strangBlock`, 4 lines) plus `simp only`.

Note `suzuki4_error_rate_sq` is stated over a general `RCLike 𝕂` and so displays
`suzuki4Step ℝ A B (↑p) n` at `𝕂 = ℝ`; that coercion is `RCLike.ofReal`, which is
definitionally the identity on `ℝ`. Verified: the quartic theorems typecheck
directly against the coerced term, so the upgrade is genuinely about the same term.

---

## 2026-07-14: L1–L3 freed of vestigial C*-algebra hypotheses

**What:** `Suzuki4ViaBCH.lean` — the three τ⁵ headline bounds now hold in **any**
complete normed algebra with `NormOneClass`, with no star structure at all.

Before: `norm_suzuki4_level2_bch`, `norm_suzuki4_level3_bch`, and
`norm_suzuki4_childs_form_via_level3` all carried
`[StarRing] [ContinuousStar] [CStarRing] [Nontrivial] [StarModule ℝ]` — and L3/L1
carried them **twice**, because `section AntiHermitianLevel3` (line 772) is nested
inside `section AntiHermitian` and re-declared the identical `variable` line.
After: signatures are `[NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸]
[CompleteSpace 𝔸]` only. Axioms unchanged (all three still
`[propext, Classical.choice, Quot.sound]`).

**How it was found.** Lean's `unusedSectionVars` linter reported the star classes
as never used in those proofs — they were auto-included section variables, not
genuine hypotheses. Removed the duplicate `variable` line and added
`omit [StarRing 𝔸] … in` to the L2/L3 bridges (`bch_w4Deriv_quintic_level2`,
`bch_w4Deriv_level3_tight`), the three headline bounds,
`norm_suzuki4_level3_le_childs_pointwise`, and two prefactor-arithmetic helpers
(`BCHPrefactors.boundSum_nonneg`, `bchTightPrefactors_le_childs`) that the
headlines call.

**The cascade.** L2 was *not* initially flagged by the linter, which looked like a
counterexample. It wasn't: L2 "used" the star instances only by passing them to
`bch_w4Deriv_quintic_level2`, which didn't need them either. Freeing the bridges
first made L2's usage evaporate. Likewise, omitting from the headlines exposed two
more call sites (`boundSum_nonneg`, `bchTightPrefactors_le_childs`) as
`synthInstanceFailed`; freeing those closed it out. Lesson: with auto-included
instance binders, "is this hypothesis used?" must be answered leaf-first — a
caller can appear to use an instance purely because its callee's signature
demands one it doesn't need.

**L4 is genuinely anti-Hermitian, and stays that way.**
`norm_suzuki4_level4_uniform` carries explicit `star A = -A`, `star B = -B`
hypotheses and really does use the C*-algebra isometry. The linter does not flag
it, correctly. So the hypothesis split is real: **L1–L3 general normed algebra,
L4 C*-algebra.** Recorded in the manuscript (§5.6 and the `tab:levels` caption).

**Why it matters.** The tight 4th-order Trotter bound — the paper's central
result — now applies to arbitrary bounded generators, not just the skew-adjoint
generators of unitary dynamics.

**Proof (three ingredients, no new machinery):**
1. **Step error** — `exists_norm_s4Func_sub_exp_le_t5` (SLICE 1, axiom-free):
   `‖S₄(τ) − exp(τ(A+B))‖ ≤ C₀·|τ|⁵` for `|τ| < δ`. Take `τ = t/n`;
   the threshold `N > |t|/δ` puts the step size inside the BCH regime.
2. **Growth bound** — `norm_suzuki4Exp_le`. Rather than grinding the
   11-factor product by hand, reuse Lean-BCH's `norm_suzuki5Product_sub_one_le`
   (which already performs the peel) plus `sum_arg_norms_le_bound`, then convert
   `‖S₄ − 1‖ ≤ exp R − 1` into `‖S₄‖ ≤ exp R` via `NormOneClass`. `s4Func` and
   `suzuki5Product` are defeq (`s4Func_eq_suzuki5Product`), as are `s4Func` and
   `suzuki4Exp` (new `s4Func_eq_suzuki4Exp`, `rfl`).
3. **Telescoping** — `norm_pow_sub_pow_le'` (Task A2). The damping factor
   collapses to a constant: `max(‖S₄(t/n)‖,‖exp((t/n)(A+B))‖)^{n−1}
   ≤ exp(|t/n|·K)ⁿ = exp(|t|·K)`. Hence `n · O(n⁻⁵) = O(n⁻⁴)`.

**Design notes:**
- Stated for `suzuki4Exp` (the object the L1–L3 headline bounds use, already
  certified as five Strang blocks by `suzuki4Exp_eq_strangProduct`), not for
  `suzuki4Step`, which carries its own built-in `1/n`.
- Hypothesis is only `IsSuzukiCubic p`. **No C*-algebra / anti-Hermitian
  structure needed** — unlike the L1–L3 tight-prefactor bounds, this holds in
  any complete normed algebra with `NormOneClass`. The `suzukiP` corollaries
  discharge even that hypothesis via `BCH.IsSuzukiCubic_suzukiP`.
- The existential `∃ N` (rather than `∀ n > 0`) is forced by the single-step
  bound's regime `|τ| < δ`; it is the honest asymptotic form.
- The constant is the crude `C₀·|t|⁵·exp(|t|·K)`, not a tight prefactor —
  tight constants are the content of L1–L3; a convergence theorem is about
  the *rate*.

**Lean gotchas hit:**
- `field_simp` fully closed the `n·(C₀·(|t|/n)⁵)·E = C₀·|t|⁵·E/n⁴` goal, so the
  customary trailing `ring` errored with "no goals".
- `div_lt_iff₀` orients as `a < c * b`, not `b * c`; needed a closing
  `_ = ε * (N₂+1) := by ring` step (`div_lt_iff₀'` would also work).

---

## 2026-05-19: Lean-BCH pin bump cf5eea3 → d455ff0 — τ⁵ headlines now axiom-free

**What:** Bumped the Lean-BCH dependency pin in `lakefile.lean` from
`cf5eea3` (Apr 26, 2026) to `d455ff0` (May 19, 2026). The new pin
includes the Lean-BCH side discharge of B1.c
(`BCH.symmetric_bch_quintic_sub_poly_axiom`) completed on the upstream
`T2-F7e` arc — the parent axiom was replaced by a polynomial-only
sub-axiom in `6ffcacb` (2026-05-10) and that polynomial-norm axiom was
itself discharged in `eae9ffc` (2026-05-11) via a `Finset.sum` refactor
that closed the per-term enumeration.

**Impact:** After the bump, `#print axioms` on all τ⁵ Lean-Trotter
headlines returns only the standard Lean foundational axioms
`[propext, Classical.choice, Quot.sound]`:

* `norm_suzuki4_childs_form_via_level3` — tight 4th-order Trotter
  (Childs (2021) Prop pf4_bound_2term form, coefficients 0.0047–0.0284)
* `norm_suzuki4_level3_bch` — tight γᵢ prefactors
* `norm_suzuki4_level2_bch` — unit-coefficient τ⁵ bound
* `bch_w4Deriv_level3_tight`, `bch_w4Deriv_quintic_level2`
* `bch_iteratedDeriv_s4Func_order4` (h4)
* `exists_norm_s4Func_sub_exp_le_t5`
* `lie_trotter`, `symmetric_lie_trotter`

**The tight 4th-order Trotter formula error bound is now fully proved
at the project level.**

**Remaining transitive axioms (gated to L4 uniform refinement only).**
The optional `bch_uniform_integrated` (and downstream
`norm_suzuki4_level4_uniform`) still depend on two surviving Lean-BCH
septic stepping stones — `BCH.symmetric_bch_septic_sub_poly_axiom` and
`BCH.norm_septic_match_residual_le_axiom`. These gate the τ⁷ uniform
refinement, not the core tight 4th-order Trotter bound.

**Doc refresh:** This commit also refreshes the top status blocks in
`CLAUDE.md` and `TODO.md`; the body audits (Track 7 status header,
prefactor-bookkeeping note, the Recommended-path-forward roadmap, the
S₄ section in README.md, and the docstrings inside
`LieTrotter/Suzuki4ViaBCH.lean`) followed in a separate doc-only pass
to remove residual "axiom" labels on the now-proved bridges.

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
