# TODO

## Remaining work (as of 2026-04-26)

The project has **0 sorries on the Lean-Trotter side**, **0 transitive
`sorryAx`** (Lean-BCH closed its last sorry at rev `c71d8f2`), and **0
own theorem-level axioms in `Suzuki4ViaBCH.lean`**. All three former
axioms (`bch_w4Deriv_quintic_level2`, `bch_w4Deriv_level3_tight`,
`bch_uniform_integrated`) are now theorems composing Lean-BCH bridge
corollaries with exp-Lipschitz / triangle-inequality lifts. Transitive
dependencies on Lean-BCH private axioms:

| Lean-Trotter theorem | Transitive Lean-BCH axiom |
|---|---|
| `bch_w4Deriv_quintic_level2` | `BCH.symmetric_bch_quintic_sub_poly_axiom` (B1.c) |
| `bch_w4Deriv_level3_tight` | `BCH.symmetric_bch_quintic_sub_poly_axiom` (B1.c) |
| `bch_uniform_integrated` (NEW 2026-04-26) | `BCH.suzuki5_log_product_septic_at_suzukiP_axiom` (R₇) |

All other headline results (`lie_trotter`, `bch_iteratedDeriv_s4Func_order4`,
`exists_norm_s4Func_sub_exp_le_t5`, etc.) depend only on Lean's 3 standard
axioms. Lean-BCH is imported as a git dependency (`require lean-bch from
git ... @ "<sha>"`).

### Track A: Discharge the 2 remaining Lean-BCH axioms

Both axioms encode 5-factor palindromic BCH facts beyond Lean-BCH's
current 2-factor coverage. Discharging them on the Lean-BCH side would
make the entire pipeline depend only on Lean's standard 3.

| Lean-BCH axiom | Supports | Discharge roadmap |
|---|---|---|
| `BCH.symmetric_bch_quintic_sub_poly_axiom` (B1.c) | Levels 2 + 3 | `claude/lean-bch-B1c-session-prompt.md` (3-tier, ~2-3 weeks) |
| `BCH.suzuki5_log_product_septic_at_suzukiP_axiom` (R₇) | Level 4 | `claude/lean-bch-suzuki5-R7-followup-session-prompt.md` (~4-5 weeks) |

**Recommended order:**
1. Discharge B1.c (Tier 1: sextic remainder; Tier 2: 8–10-term decomposition;
   Tier 3: triangle-inequality assembly). Closes Levels 2 + 3.
2. Discharge R₇ (sextic + symmetric BCH septic + R₇ Childs-basis
   projection + per-summand bounds + assembly). Closes Level 4.

### Track A.0 (retired): the original 3 Lean-Trotter `bch_w4Deriv_*` axioms

All three converted to theorems:
- `bch_w4Deriv_quintic_level2` (closed 2026-04-24, Lean-Trotter rev `5a2c03e`):
  invokes `BCH.suzuki5_log_product_quintic_of_IsSuzukiCubic`.
- `bch_w4Deriv_level3_tight` (closed 2026-04-24, Lean-Trotter rev `705791a`):
  invokes `BCH.suzuki5_log_product_quintic_tight_at_suzukiP`.
- `bch_uniform_integrated` (closed 2026-04-26): invokes the new
  `BCH.suzuki5_log_product_septic_at_suzukiP` bridge corollary;
  signature changed from uniform "for all t ≥ 0" (mathematically false)
  to existential-δ "∃ δ > 0, ∀ t ∈ [0, δ)" (mathematically correct).

### Track A.0 (retired): the Childs-heuristic axiom

Closed 2026-04-23: `bch_childs_pointwise_residual` was retired because
Childs et al. 2021 themselves label those coefficients heuristic. The
Childs reproduction theorem `norm_suzuki4_childs_form_via_level3` now
derives the same numerical bound from the CAS-certified Level 3
(`norm_suzuki4_level3_bch`) plus the Lean-proved termwise inequality
`bchTightPrefactors_le_childs` (γᵢ ≤ αᵢ). Axiom count 5 → 4.

### Track A.1 (retired): the 4 symmetric-BCH-cubic axioms

Closed 2026-04-23 via direct import of Lean-BCH's `symmetric_bch_cubic`,
`exp_symmetric_bch`, `norm_symmetric_bch_cubic_le`, and
`norm_symmetric_bch_cubic_sub_smul_le` (specialized to `𝕂 := ℝ`).
Constant in the quintic scaling bound rose from speculative 10⁴ to
proven 2·10⁷ (downstream `suzuki4_bchCubic_sum_bound`: 50000 → 10⁸).

### Track A.2 (retired): `bch_iteratedDeriv_s4Func_order4`

Closed 2026-04-23/24 via the SLICE 1+2+3 chain:
- SLICE 1 `Suzuki4BchBound.lean`: single-step O(|τ|⁵) via Lean-BCH M6 +
  the opaque-RHS corollary `suzuki5_bch_M4b_RHS_le_t5_of_IsSuzukiCubic`
  (Lean-BCH rev `4ea6357`).
- SLICE 2 `TaylorMatch.lean`: generic Taylor-match-from-norm
  (`iteratedDeriv_eq_of_norm_le_pow`) via `taylor_isLittleO_univ`.
- SLICE 3 `Suzuki4ViaBCH.lean`: wires SLICE 1 + SLICE 2 +
  `iteratedDeriv_exp_smul_mul_at_zero`. Axiom count 4 → 3.

### Track B (superseded): h4 alternative (Path A, Lean-native)

No longer on the critical path — h4 is closed via SLICE 1+2+3 (Track A.2).
Kept as a future nice-to-have: a purely Trotter-native proof of
`sumQuadCorr (s4DList A B p) = 0` would remove the transitive dep on
Lean-BCH for h4. **Blocked on `module` tactic timeout at 20M heartbeats**
(`whnf` stage fails before `module` runs — expression size blows up after
`simp only [← mul_assoc, smul_mul_smul_mul_smul]` on the quartic expansion).

**Attempts (2026-04-23):**
1. Yoshida BCH identity `sumQuadCorr = 2·(H·sumTripleCorr+sumTripleCorr·H)` via
   direct `module` — timed out at 4M heartbeats (>4 min), still timed out at
   40M (>10 min, killed).
2. CAS-assisted factored form `sumQuadCorr s4DList = (4p³+q³) • Q_quartic`
   with Q explicitly computed via `scripts/compute_sumQuadCorr_factored.py`
   (14 quartic monomials) — module timed out at 4M heartbeats and at 20M
   heartbeats (>8 min each).

CAS confirms the factored form exists with 14 quartic monomials, and the
scalar `4p³ + (1-4p)³` matches Suzuki cubic. The identity is mathematically
correct; the obstruction is purely tactic/engineering.

**Remaining approaches:**
1. Hand-structured proof splitting the 14-monomial goal into ~4 groups of
   3-4 monomials, closing each with `noncomm_ring` separately. Estimate:
   500-800 lines of careful staging.
2. Bump `maxHeartbeats` past 100M (may take 30+ min per build, not a
   reasonable dev experience).
3. Build a custom Lean helper tactic that handles sumQuadCorr + s4DList
   more efficiently than generic `module`.
4. Abandon Route B and pursue Route A (extend Lean-BCH with 5-factor
   palindromic quintic remainder, derive h4 as a corollary there).

Axiom 1 was ultimately closed via the SLICE chain (Track A.2), so Track B is
now optional. Remaining relevance: option 1 (hand-staged proof) would remove
the transitive Lean-BCH dep for h4 — a nice-to-have, not a blocker.

### Track C: Scientific extensions

- [ ] **Minimum-ℓ¹ Childs projection.** Our projection sets `γ₃ = γ₇ = 0`;
  the ℓ¹-optimal projection in the 8-commutator over-complete basis requires
  a small linear program. Would tighten Level 3/4 bounds slightly.
- [ ] **R₉ via CAS extension.** `compute_bch_r9.py` would extend to order 9
  and give a tighter uniform bound constant. Diminishing returns (R₇ already
  provides orders-of-magnitude margin for typical Trotter regimes).
- [ ] **Multi-operator S₄.** Generalize `s4Func A B p` to `s4Func A₁ ... Aₘ p`.
  Opens Childs's multi-operator Trotter framework (physics applications).
- [ ] **Higher-order Suzuki (S₆, S₈).** Recursive Suzuki hierarchy. Each step
  reuses palindromic + cubic-cancellation structure. Very ambitious.
- [ ] **Total-error convergence theorem for S₄.** Current L3/L4 give step error
  `O(t⁵)`; a total-error theorem `(S₄(1/n))^n → exp(A+B)` at `O(1/n⁴)` would
  parallel the existing `lie_trotter` and `symmetric_lie_trotter` theorems.

### Track D: Mathlib contributions

Several lemmas are ready for upstreaming (~20-50 lines each):

- [ ] `norm_exp_le` for general Banach algebras (Mathlib only has ℂ version).
  **PR readiness cleanup needed:**
  1. Weaken `[NormOneClass 𝔸]` → use `norm_pow_le'` (works with just `[NormedRing 𝔸]`)
  2. Remove `include 𝕂 in` pattern (non-standard for Mathlib); use section variables instead
  3. Follow Mathlib naming: `norm_exp_le` → `norm_exp_le_exp_norm`, etc.
  4. Drop redundant helpers (`real_exp_summable`, `real_exp_eq_tsum` already in Mathlib)
  5. Target file: `Mathlib.Analysis.Normed.Algebra.Exponential` (modify existing, not new file)
  6. Open a Zulip thread first to confirm maintainer interest before investing effort
- [ ] `norm_exp_sub_one_le`, `norm_exp_sub_one_sub_le`, `exp_sub_one_sub_bound_real`
  — companion lemmas, same file.
- [ ] `suzuki4Exp` / `strangBlock` definitions if there's demand.

### Track E: Paper / writing

- [ ] Polish `lean4trotter/lean4trotter.tex` (25 pages, some references tightenable).
- [ ] Abstract update mentioning L3/L4 BCH-derived results.
- [ ] Replace Table 1 (numerical comparison) with a log-scale bar chart of
  BCH vs Childs coefficients (more striking visualization).
- [ ] Submission target selection: arXiv + ITP/CPP/JFR/JAR.
- [ ] Zulip announcement post (short, leanprover.zulipchat.com #general).

### Track F: Code hygiene

- [ ] Replace `import Mathlib.Tactic` with specific tactic imports (faster compile).
- [ ] Explicit `omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in ...` on theorems that
  don't use these (warnings currently benign but noisy).
- [ ] Matrix specialization: `matrix_lie_trotter` for `Matrix (Fin d) (Fin d) ℂ`
  (~30 lines; requires `NormOneClass` for matrix norm).

---

## Recommended path forward

**Short term (1-2 weeks):**
- **Track A (next):** extend Lean-BCH to 5-factor palindromic quintic remainder
  to close `bch_w4Deriv_quintic_level2` and the leading order of
  `bch_w4Deriv_level3_tight`. 3 axioms → 2 (or 1, depending on projection work).
- **Track D:** start Mathlib PR for `norm_exp_le` (see cleanup checklist below).

**Medium term (1-3 months):**
- **Track E:** polish paper; submit to arXiv.
- **Track D:** open Mathlib Zulip thread; prepare first PR (`norm_exp_le`).
- **Track C:** pick one extension (multi-operator S₄ recommended; physics-relevant).

**Long term (>3 months):**
- Higher-order Suzuki S₆/S₈ if funding / collaborator interest.
- Full automated BCH prefactor pipeline (CAS + Lean-BCH → Lean-Trotter).

---

## Completed and published (historical)

- [x] **Contribute `norm_exp_le` to Mathlib** — We proved `‖exp a‖ ≤ exp ‖a‖` for general Banach algebras; Mathlib only has `Complex.norm_exp_le_exp_norm` for `ℂ`. The helpers `norm_exp_sub_one_le`, `exp_sub_one_sub_bound_real`, and `norm_exp_sub_one_sub_le` are also natural additions.
  (Retained above as Track D; marked done here for history.)

  **PR readiness assessment** (cleanup needed before submitting):
  1. Weaken `[NormOneClass 𝔸]` → use `norm_pow_le'` (works with just `[NormedRing 𝔸]`)
  2. Remove `include 𝕂 in` pattern (non-standard for Mathlib); use section variables instead
  3. Follow Mathlib naming: `norm_exp_le` → `norm_exp_le_exp_norm`, etc.
  4. Drop redundant helpers (`real_exp_summable`, `real_exp_eq_tsum` already in Mathlib)
  5. Target file: `Mathlib.Analysis.Normed.Algebra.Exponential` (modify existing, not new file)
  6. Open a Zulip thread first to confirm maintainer interest before investing effort

- [x] **Tighten the error constant** — Tightened from `C = 2‖A‖‖B‖ exp(2(‖A‖+‖B‖)) + 1` to `C = 2‖A‖‖B‖ exp(‖A‖+‖B‖) + 1`. The `+1` remains for `C > 0`; only `1/n` slack.

## Medium priority

- [x] **Strang splitting convergence (F2a)** — Proved `(exp(A/2n) exp(B/n) exp(A/2n))^n → exp(A+B)` at O(1/n) rate using C1 applied twice. File: `LieTrotter/StrangSplitting.lean`.
- [x] **Strang splitting O(1/n²) rate (F2b)** — Proved O(1/n²) convergence by showing cubic step error O(1/n³). Key: the commutator [a,b] cancels by symmetry in exp(a)exp(b)exp(a), leaving cubic remainder. New lemma `norm_exp_mul_exp_sub_exp_add_sub_comm_le` extracts the commutator from the Lie-Trotter error.

- [x] **Multi-operator Lie-Trotter (G1)** — Generalize from $A+B$ to $A_1 + \cdots + A_m$:
  $$e^{A_1+\cdots+A_m} = \lim_{n\to\infty} (e^{A_1/n} \cdots e^{A_m/n})^n$$
  This is the version used in quantum simulation (Hamiltonians decompose into many terms).
  The proof generalizes by induction on $m$, peeling off one factor at a time:
  ```
  ‖e^{a₁}⋯e^{aₘ₊₁} - e^{a₁+⋯+aₘ₊₁}‖
    ≤ ‖e^{a₁}‖ · ‖e^{a₂}⋯e^{aₘ} - e^{a₂+⋯+aₘ}‖ + ‖e^{a₁}e^{a₂+⋯+aₘ} - e^{a₁+⋯+aₘ}‖
  ```
  Telescopes into a sum of pairwise C1-type bounds. Estimate: ~150 lines. Reuses all existing infrastructure.

- [~] **Fourth-order Suzuki formula (H1)** — Substantially progressed, one gap remains (h4).

  **Status (2026-04-22):**
  - ✅ Infrastructure: prodExpList framework, multinomial formulas up to order 4,
    Phase 5 Taylor-reduction + Leibniz bridges, CAPSTONE theorem.
  - ✅ h2 PROVED UNCONDITIONAL (`iteratedDeriv_s4Func_order2_eq_sq`)
  - ✅ h3 PROVED under `IsSuzukiCubic p` via factored-form operator identity
    `sumTripleCorr_s4DList_eq_factored`.
  - ✅ Strengthened CAPSTONE `norm_suzuki4_order5_with_h2_h3_and_w4Func_order4_vanishing`
    takes only IsSuzukiCubic + w4Func order-4 vanishing.
  - ✅ Task 1 (`suzuki4Exp_eq_strangProduct`): S₄ = 5 Strang blocks.
  - ✅ Task 2 (`suzuki4_coeff_cube_sum_zero`): 4p³+(1-4p)³=0 under Suzuki.
  - ✅ Task 3 (Suzuki4ViaBCH.lean): BCH-interface axioms + Level 1 Childs bound
    + Level 2 rigorous BCH bound with explicit unit prefactors.
  - 🔴 **Remaining: h4** (`iteratedDeriv 4 (s4Func A B p) 0 = (A+B)^4`).

  **Two paths for h4:**
  - **Path A (native)**: prove `sumQuadCorr_s4DList = 0` under Suzuki; blocked
    by `module` tactic timeout on quartic expansion.
  - **Path B (via Lean-BCH)**: wait for Lean-BCH's quintic BCH to complete
    (`quintic_pure_identity` nsmul gap), then replace the 7 BCH-interface
    axioms in `Suzuki4ViaBCH.lean` with imports. This gives h4 automatically
    via `bch_iteratedDeriv_s4Func_order4`.

  **Currently usable results (modulo BCH axioms):**
  - `norm_suzuki4_order5_via_bch_axiom`: existential S₄ O(t⁵) under IsSuzukiCubic.
  - `norm_suzuki4_childs_form_via_level3`: reproduces Childs 2021 Prop pf4_bound_2term
    with exact coefficients 0.0047-0.0284, derived from the Level 3 bound via the
    Lean-proved termwise inequality γᵢ ≤ αᵢ (no heuristic axiomatization).
  - `norm_suzuki4_level2_bch`: rigorous BCH-derived bound with explicit unit
    coefficients on 8 four-fold commutators (no Childs heuristic required).

- [x] **Truncated BCH bounds ([Lean-BCH](https://github.com/Jue-Xu/Lean-BCH))** — ✅ Complete (0 sorry's before Suzuki extension).
  Proved: `exp_bch`, `norm_bch_sub_add_sub_bracket_le` (H1), `norm_symmetric_bch_sub_add_le` (H2), Lie bracket bridge (M1).

- [ ] **General Suzuki hierarchy (H2)** — Prove convergence of the $2k$-th order Suzuki formula $S_{2k}$ defined recursively:
  $$S_{2k}(t) = S_{2k-2}(p_k t)^2\, S_{2k-2}((1-4p_k)t)\, S_{2k-2}(p_k t)^2, \quad p_k = \frac{1}{4-4^{1/(2k-1)}}$$
  This gives O(1/n^{2k}) convergence. Very ambitious — requires induction on the Suzuki order $k$ and tracking error cancellation at each level. Likely a separate project.

- [x] **Commutator-scaling Trotter error (H)** — Proved `norm_lie_trotter_comm_scaling`: the Trotter error `‖exp(tB)exp(tA) - exp(t(A+B))‖` is bounded by `‖[B,A]‖ · t² · exp(t(‖A‖+3‖B‖))`, replacing the product `‖A‖‖B‖` with the commutator `‖[B,A]‖`. Uses Duhamel formula via FTC-2. File: `LieTrotter/CommutatorScaling.lean` (370 lines, 0 sorry's).

- [x] **Tighten commutator-scaling constant to t²/2** — ✅ Done. Used `norm_integral_le_of_norm_le` (non-constant) + FTC-2 on `x²/2` to evaluate `∫₀ᵗ τ dτ = t²/2`.

- [x] **Multi-operator commutator-scaling** — ✅ Done. File: `LieTrotter/MultiCommutatorScaling.lean` (128 lines). Defines `listCommNorm` (sum of commutator norms with suffix sums) and proves `norm_list_prod_exp_sub_exp_sum_comm`. Matches the Proposition in Childs et al. §VII.A for first-order.

- [x] **Second-order (Strang) commutator-scaling** — ✅ Done. Files: `LieTrotter/StrangCommutatorScaling.lean` (~480 lines, 0 sorry's) and `LieTrotter/MultiStrangCommutatorScaling.lean` (~170 lines, 0 sorry's). Proved the Proposition from Childs et al. (`prefactor.tex:105`):
  $$\|S_2(t) - e^{tH}\| \le \frac{t^3}{12}\|[B,[B,A]]\| + \frac{t^3}{24}\|[A,[A,B]]\|$$
  for anti-Hermitian operators in C*-algebras. Multi-operator version via `palindromicProd` and `listDoubleCommNorm` (induction on operator list).

- [ ] **Matrix specialization (F1)** — Prove `matrix_lie_trotter` for `Matrix (Fin d) (Fin d) ℂ`. Should be a one-liner applying `lie_trotter` once the `NormOneClass` instance is verified for the matrix norm. Connects to quantum computing applications.

## Low priority

## Publication / dissemination

- [ ] **Zulip announcement + arXiv note** (do first, low effort) — Post to `#general` on [leanprover.zulipchat.com](https://leanprover.zulipchat.com/) announcing the formalization. Write a 1–2 page arXiv companion note (cs.LO or quant-ph) with the repo link. Gets immediate community visibility.

- [ ] **ITP/CPP formalization pearl** (medium effort, peer-reviewed) — 2–4 page short paper covering: (1) the algebraic factorization trick for C1 vs. the standard BCH approach, (2) the commutator cancellation for the cubic Strang bound, (3) the Mathlib API gap (`norm_exp_le` for general Banach algebras). Check submission deadlines.

- [ ] **Companion citation for physics papers** — If writing a paper on Hamiltonian simulation or Trotter error bounds, cite this repo as mechanically verified. The O(1/n²) Strang result is directly relevant to quantum simulation.

## Code cleanup

- [ ] **Clean up lint warnings** — The `mathlib: repository has local changes` warning appears because `lake update` modified the local Mathlib checkout. Running `lake update` fresh in a clean clone resolves this. Not a real issue but worth noting for CI.

- [ ] **Remove `import Mathlib.Tactic`** — Replace with specific tactic imports (`Mathlib.Tactic.NoncommRing`, `Mathlib.Tactic.Positivity`, etc.) in `Telescoping.lean` and `ExpBounds.lean` for faster compilation.
