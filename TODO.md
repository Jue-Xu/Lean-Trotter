# TODO

## Remaining work (as of 2026-08-02)

The project has **0 sorries on the Lean-Trotter side**, **0 own
theorem-level axioms in `Suzuki4ViaBCH.lean`**, and, with Lean-BCH pinned
at `05e8c52` (2026-07-28), **0 transitive non-foundational axioms**, including
the complete τ⁷/L4 chain. The two former Lean-BCH septic stepping stones
are now proved theorems.

`#print axioms` on each headline returns only Lean's 3 standard
foundational axioms `[propext, Classical.choice, Quot.sound]`:

- `norm_suzuki4_childs_form_via_level3` ✓ (order-only Childs-labelled corollary)
- `norm_suzuki4_level3_bch` ✓ (order-only Level 3 corollary)
- `norm_suzuki4_level2_bch` ✓ (order-only Level 2 corollary)
- `bch_w4Deriv_level3_tight` ✓
- `bch_w4Deriv_quintic_level2` ✓
- `bch_iteratedDeriv_s4Func_order4` ✓
- `exists_norm_s4Func_sub_exp_le_t5` ✓
- `bch_uniform_integrated` ✓ (complete τ⁷ bridge)
- `norm_suzuki4_level4_uniform` ✓ (L4 uniform refinement)
- `suzuki4_total_error_quartic` ✓ (S₄ total error O(1/n⁴), NEW 2026-07-14)
- `suzuki4_convergence_quartic` ✓ (S₄ convergence, NEW 2026-07-14)
- `lie_trotter` ✓

The convergence hierarchy is now complete: `lie_trotter` (O(1/n)) →
`symmetric_lie_trotter` (O(1/n²)) → `suzuki4_convergence_quartic` (O(1/n⁴)).

The B1.c quintic axiom (`BCH.symmetric_bch_quintic_sub_poly_axiom`) was
discharged on the Lean-BCH side in May 2026; with the pin bump it no
longer appears in any τ⁵ headline's dependency tree.

### Track A (completed): L4 uniform refinement and the septic chain

The L4 uniform bound `bch_uniform_integrated` and downstream
`norm_suzuki4_level4_uniform` are axiom-free at Lean-BCH pin `05e8c52`.
Both former septic stepping stones were discharged upstream on 2026-07-28:

| Former Lean-BCH stepping stone | Status at `05e8c52` | Supports |
|---|---|---|
| `BCH.symmetric_bch_septic_sub_poly_axiom` | Retired; replacement chain proved | L4 (`bch_uniform_integrated`) |
| `BCH.norm_septic_match_residual_le_axiom` | Retired; replacement chain proved | L4 (`bch_uniform_integrated`) |

This is retained as history only; there is no active septic-axiom discharge
task. `#print axioms` for the L4 headlines now reports only Lean's three
standard foundational axioms.

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
  Its former upstream septic dependencies were subsequently discharged at
  Lean-BCH pin `05e8c52` on 2026-07-28.

### Track A.0 (retired): the local Childs-bound axiom

Closed 2026-04-23: `bch_childs_pointwise_residual` was retired because
the project no longer needs to assume the published coefficient form.
Childs et al. (2021), arXiv Proposition J.1, prove a rigorous bound with
coefficients in the range 0.0046–0.0284; the coefficients are not claimed to
be tight. `norm_suzuki4_childs_explicit` carries those coefficients (plus the
required `K′τ⁶` remainder) and follows from `norm_suzuki4_level3_explicit` plus
the Lean-proved inequality `bchTightPrefactors_le_childs` (γᵢ ≤ αᵢ).
`norm_suzuki4_childs_form_via_level3` is retained as an order-only alias.
Axiom count 5 → 4.

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
- [x] **Total-error convergence theorem for S₄.** ✅ Done 2026-07-14,
  `LieTrotter/Suzuki4Convergence.lean` (0 sorries, axiom-free).
  `suzuki4_total_error_quartic`: `‖S₄(t/n)ⁿ − exp(t(A+B))‖ ≤ C/n⁴` for `n ≥ N`;
  `suzuki4_convergence_quartic`: `S₄(t/n)ⁿ → exp(t(A+B))`. Compounds the
  SLICE-1 step bound `exists_norm_s4Func_sub_exp_le_t5` via telescoping
  (`norm_pow_sub_pow_le'`) plus a new growth bound `norm_suzuki4Exp_le`.
  Completes the hierarchy O(1/n) → O(1/n²) → O(1/n⁴). Hypothesis is only
  `IsSuzukiCubic p`; the `*_suzukiP` corollaries are hypothesis-free.

- [x] **`suzuki4Step` bridge + O(1/n⁴) upgrade.** ✅ Done 2026-07-14 (same file).
  `suzuki4Step_eq_suzuki4Exp : suzuki4Step ℝ A B p n = suzuki4Exp A B p (1/n)`,
  reusing `suzuki4Exp_eq_strangProduct` for the four junction merges — only the
  scalar identity `strangStep(c,n) = strangBlock(c/n)` was new. Yields
  `suzuki4Step_total_error_quartic` and `suzuki4Step_convergence_quartic`,
  which upgrade `suzuki4_error_rate_sq` / `suzuki4_convergence` (O(1/n²)) to
  O(1/n⁴) on the *same* object.

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

- [x] Rebuild and review the 35-page manuscript; synchronize the abstract,
  quartic convergence, axiom status, QBlue related work, and source links.
- [ ] Replace Table 1 (numerical comparison) with a log-scale bar chart of
  BCH vs Childs coefficients (optional; the existing table is release-ready).
- [ ] Submit the current manuscript to arXiv and select a journal/conference
  target (ITP/CPP/JFR/JAR).
- [ ] Zulip announcement post (short, leanprover.zulipchat.com #general).

### Track F: Code hygiene

- [ ] Replace `import Mathlib.Tactic` with specific tactic imports (faster compile).
- [ ] Explicit `omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in ...` on theorems that
  don't use these (warnings currently benign but noisy).
- [x] Matrix specializations, including `matrix_lie_trotter` and Suzuki state
  error, in `LieTrotter/MatrixCorollaries.lean`.

---

## Roadmap (2026-08-02 status update)

Consolidated from a four-way survey: manuscript open-issue audit, Lean
statement audit, literature novelty check, and pinned-Mathlib gap analysis.
The "quick wins" cluster and two reproducible numerical experiments
**landed 2026-07-17**: 7 new axiom-free modules
(`Suzuki4UnitaryTotalError`, `StrangTotalErrorCommScaling`,
`Suzuki4Commute`, `TrotterStepCount`, `MatrixCorollaries`, `Suzuki4GapClosers`,
`PrefactorStrict`; `#print axioms` reports only the 3 standard axioms on all
23 new headline theorems). The committed experiment artefacts are
`scripts/sweep_strang_alignment.py` with
`claude/strang_alignment_sweep.csv`, and `scripts/test_r5_gain.py` with
`claude/s4_r5_gain.csv`; the independent Strang check is
`scripts/verify_strang_alignment_independent.py`. They resolve the appendix
open issue positively (Strang tight-bound gain 9–50% on the sampled spin
chains) and pass the S₄ ‖R₅‖ numerical gate (gain 8–86%). A polished
bound-versus-true-error benchmark remains optional work below.

### Novelty context (literature check, updated 2026-08-02)

- QBlue's public Rocq artifact (Zenodo DOI 10.5281/zenodo.15852130) contains
  theorem declarations named `lie_trotter_error_bound` and
  `suzuki_second_order_error_bound`. Accordingly, do **not** claim the first
  machine-checked higher-order Trotter bound without qualification. The
  manuscript now scopes novelty to the first kernel-checked norm-convergence
  proof found, with no project-specific axioms, for the Lie–Trotter sequence
  on arbitrary elements of a complete normed algebra, while separately
  presenting the explicitly audited higher-order and commutator-scaled
  hierarchy.
- No published work analytically tightens the rigorous, but not proven tight,
  S₄ prefactors in Childs et al. (2021), arXiv Proposition J.1
  (coefficient range 0.0046–0.0284)
  (checked: arXiv:2210.15817 numerically optimizes *other* formulas;
  2409.16634 improves time-scaling, not the τ⁵ prefactor; 2510.11621 bounds
  commutator norms by Monte Carlo; 2606.30738 changes the error metric).
  γᵢ ≤ αᵢ is a novel analytic claim — foreground it.

### Medium formalization targets (weeks each)

- [ ] **Trotter error LOWER bound (two-sided theory).** Formalize
  `‖e^{tA}e^{tB} − e^{t(A+B)}‖ ≥ (t²/2)‖[A,B]‖ − C·t³` with explicit `C`
  (reverse triangle inequality + existing ExpBounds Taylor machinery; style of
  arXiv:2410.03059), plus a concrete nilpotent-matrix witness of `≥ c/n` total
  error. No prover has any simulation lower bound — highest novelty-per-line
  item. Strang analogue at t³ as a follow-up.
- [ ] **Backward-error / effective-Hamiltonian theorem.**
  `∃ H_eff, S₄(τ) = exp(τ • H_eff) ∧ ‖H_eff − (A+B)‖ ≤ C·τ⁴` (and S₂ at τ²).
  Lean-BCH's `suzuki5_log_product_*` already identifies log S₄(τ) as an
  explicit element; only the exp/log inversion near 0 + a norm bound remain.
  First formalized backward-error result for product formulas.
- [ ] **S₄ norm-of-difference bound.** In a general normed algebra the
  operator-difference lift has the prospective form
  `‖S₄(t) − e^{tH}‖ ≤ ‖R₅‖t⁵ + K′t⁶`; exponentiation produces an order-six
  cross term. An order-seven remainder should be pursued only through a
  skew-adjoint/unitary Duhamel route. Either form would dominate the current
  triangle-inequality Level 3 leading coefficient. GATE PASSED (2026-07-17,
  `scripts/test_r5_gain.py`, data in `claude/s4_r5_gain.csv`):
  ‖R₅‖/Σγ‖C‖ = 0.14–0.92 on the sampled spin chains
  (gain 8–86%; a further ~1.4–7× beyond Level 3) — worth formalizing.
- [ ] **Explicit constants in L4 + the quartic total error.** Replace the
  existential δ, C, N with computed values (exp-Lipschitz inflation is
  computable; the audit notes say "nothing but effort blocks it"). Needed for
  verified resource estimation.
- [ ] **k-local / lattice commutator-counting corollary.** For operator lists
  where non-adjacent terms commute (nearest-neighbour chains), collapse
  `listCommNorm`/`listDoubleCommNorm` from O(L²) to O(L) overlapping pairs ⇒
  per-site (extensive) error constants. Only needs a Finset counting argument
  on top of the existing multi-operator machinery.
- [ ] **Minimum-ℓ¹ Childs projection** (Track C item; closes manuscript
  Caveat 1): 2-variable LP over valid projections of R₅ onto the 8-commutator
  over-complete basis; re-certify per-i rationals by the existing `nlinarith`
  pattern.
- [ ] **Native Trotter h4** (Track B option 1): hand-staged 14-monomial proof
  of `sumQuadCorr (s4DList A B p) = (4p³+(1−4p)³) • Q`, removing Lean-BCH from
  the τ⁵ critical path. CAS-verified already; ~500–800 lines of staging.
- [ ] **R₉ CAS extension** (Track C item): mechanical extension of
  `compute_bch_r7.py`; substantiates the "pipeline iterates" claim.

### Research-project scale (pick at most one at a time)

- [ ] **Multi-operator S₄** (Track C item, recommended first): L-term
  Hamiltonians, Childs Theorem-10 shape — required before any real physical
  resource estimate. Multi-op induction templates exist through Strang.
- [ ] **S₂ₖ recursion at O(1/n^{2k})**: first machine-checked arbitrary-order
  product formula; SLICE 2 (`iteratedDeriv_eq_of_norm_le_pow`) is already
  order-generic; the general-order BCH step likely needs Lean-BCH extension.
- [ ] **Multi-product / Richardson-extrapolated formulas** (Watson–Watkins
  arXiv:2408.14385, Faehrmann arXiv:2101.07808): deterministic MPF core is
  pure Banach-algebra triangle-inequality work; first formalized
  error-mitigation guarantee.
- [ ] **State-dependent (vector-norm) Trotter bounds**: port Duhamel to
  operators acting on a state; long-range: interference/entanglement bounds
  (arXiv:2406.02379) and the error-variance line of arXiv:2604.13486 (Zhang,
  Xu, Zhao, Zhou) — "we formalize our own bound".
- [ ] **qDRIFT stage 1**: Campbell's mixing lemma + expected-channel bound for
  finite sampling distributions (Finset-weighted sums, no measure theory);
  stage 2 (single-realization concentration) needs matrix martingales.
- [ ] **Symmetry-protected / Zeno-subspace bound** (arXiv:2006.16248): algebra
  with an idempotent commuting with H; norm-level Zeno lemma is publishable
  alone.
- [ ] **C₀-semigroups → Trotter–Kato** (unbounded generators): Mathlib has
  zero one-parameter-semigroup theory (no Hille–Yosida, no Stone). Stage 1
  (definitions + bounded-generator case ↔ this project's exp API) is a
  self-contained Mathlib PR; stage 2 is multi-quarter.

### Mathlib PR cluster (verified against pin `06a46dae`)

- [ ] `norm_exp_le_exp_norm` family — upstream still has only the ℂ version
  (`Analysis/Complex/Exponential.lean:480`). State over
  `[NormedRing][NormedAlgebra ℝ][NormOneClass][CompleteSpace]` (NOT the
  ℚ-algebra form — comparing against `Real.exp ‖a‖` needs ℝ-structure).
  Cleanup checklist in Track D below.
- [ ] `norm_exp_smul_of_skewAdjoint` (`‖exp(t•a)‖ = 1`, C*-algebra): ~10-line
  PR composing Mathlib's `exp_mem_unitary_of_mem_skewAdjoint`
  (`Analysis/Normed/Algebra/Exponential.lean:540`) with unitary-norm-one; the
  norm corollary is absent upstream.
- [ ] **`lie_trotter` itself** (new `Analysis/Normed/Algebra/TrotterProduct.lean`):
  `grep -ri trotter` over Mathlib returns zero hits; include
  `norm_pow_sub_pow_le'` and `norm_exp_mul_exp_sub_exp_add'`. Strang as
  follow-up.
- [ ] **Duhamel integral representation** (`exp_conj_sub_eq_integral`,
  `lie_trotter_integral_error`, first-order commutator scaling): no
  variation-of-parameters identity for the algebra exponential exists
  upstream at all.
- [ ] **BCH itself from Lean-BCH**: Mathlib's `Algebra/Lie/` has no BCH
  formula in any form — bigger hole than the exp lemmas, and eliminates the
  pinned-external-repo trust caveat for this project's headlines.
- [ ] `Matrix.det (exp A) = exp (trace A)`: pre-approved TODO in Mathlib's
  `MatrixExponential.lean`; this project owns the derivative-of-exp
  technology the ODE proof needs.

### Infrastructure

- [ ] **CI + axiom-audit harness** (no `.github/` exists): `lake build` on
  push, a script asserting `#print axioms` on the ~10 headlines returns
  exactly `[propext, Classical.choice, Quot.sound]` for every audited theorem,
  including L4; `#check @thm` snapshots for every manuscript-cited theorem so
  statement drift fails CI; and the committed CAS checks, including
  `scripts/verify_strangblock_degree7.py` and
  `scripts/verify_strang_alignment_independent.py`.
  Tag a release pinning Lean-BCH `05e8c52`.
- [ ] **Optional bound-vs-true-error benchmark figure** for the manuscript:
  true `‖S(t/n)ⁿ − e^{tH}‖` versus the certified bounds, on a log-log scale
  for small spin chains. This is not part of the committed reproducibility
  bundle; if promoted into the paper, commit its generator, data, figure, and
  methodology together. The existing coefficient table may instead be kept.
- [x] **Manuscript related-work paragraph:** QBlue (arXiv:2509.18583) is cited
  and the first-machine-checked-higher-order claim is scoped precisely.

---

## Recommended path forward

**Short term:**
- Complete the release build/axiom audit, publish the repository, and submit
  the current 35-page manuscript to arXiv.
- Optionally start the Mathlib upstream discussion for `norm_exp_le`.
- Announce the axiom-free τ⁵/τ⁷ and O(1/n⁴) results on Zulip.

**Medium term (1-3 months):**
- Submit the manuscript to a peer-reviewed venue.
- **Track D:** open Mathlib Zulip thread; prepare first PR (`norm_exp_le`).
- **Track C:** pick one extension (multi-operator S₄ recommended; physics-relevant).

**Long term (>3 months):**
- Higher-order Suzuki S₆/S₈ if funding / collaborator interest.
- Full automated BCH prefactor pipeline (CAS + Lean-BCH → Lean-Trotter).

---

## Completed project milestones (historical)

- [x] **Prove `norm_exp_le` locally.** The general Banach-algebra theorem and
  companion remainder bounds are in this project. Upstream contribution to
  Mathlib remains open under Track D above.

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
  Telescopes into a sum of pairwise C1-type bounds and reuses the existing infrastructure.

- [x] **Fourth-order Suzuki formula (H1)** — ✅ Done, axiom-free through
  the τ⁷/L4 refinement.

  **Status (2026-07-28):** At Lean-BCH pin `05e8c52`, all τ⁵ headlines
  (L1 Childs-labelled order bound, L2 unit-bound route, L3 certified γᵢ) and the τ⁷/L4
  uniform refinement depend only on the standard Lean foundational axioms.
  Closure path:
  - ✅ Infrastructure: prodExpList framework, multinomial formulas up to order 4,
    Phase 5 Taylor-reduction + Leibniz bridges, CAPSTONE theorem.
  - ✅ h2 PROVED UNCONDITIONAL (`iteratedDeriv_s4Func_order2_eq_sq`).
  - ✅ h3 PROVED under `IsSuzukiCubic p` via factored-form operator identity
    `sumTripleCorr_s4DList_eq_factored`.
  - ✅ h4 PROVED via the Lean-BCH SLICE 1+2+3 chain (Track A.2, retired).
  - ✅ Task 1 (`suzuki4Exp_eq_strangProduct`): S₄ = 5 Strang blocks.
  - ✅ Task 2 (`suzuki4_coeff_cube_sum_zero`): 4p³+(1-4p)³=0 under Suzuki.
  - ✅ Task 3 (Suzuki4ViaBCH.lean): the 3 former `bch_w4Deriv_*` axioms are
    now theorems composing Lean-BCH bridge corollaries (May 2026).
  - ✅ L4 upstream closure: both former septic stepping stones are proved at
    Lean-BCH pin `05e8c52` (2026-07-28).

  **Path B (native Trotter h4)** — superseded but kept as a nice-to-have.
  See "Track B (superseded)" above for the engineering details of the
  open `sumQuadCorr_s4DList = 0` proof, which would remove the external
  Lean-BCH dependency from h4. This is an architectural nice-to-have, not
  an axiom-discharge task: both imported chains already resolve to theorems.

  **Headline results (axiom-free):**
  - `norm_suzuki4_childs_form_via_level3`: order-only alias of Level 3;
    `norm_suzuki4_childs_explicit` carries Childs's rigorous arXiv
    Proposition J.1 coefficients plus `K′τ⁶`.
  - `norm_suzuki4_level2_bch`: order-only corollary;
    `norm_suzuki4_level2_explicit` carries unit coefficients plus `K′τ⁶`.
  - `norm_suzuki4_level3_bch`: order-only corollary;
    `norm_suzuki4_level3_explicit` carries the γᵢ prefactors plus `K′τ⁶`.

- [x] **Truncated BCH bounds ([Lean-BCH](https://github.com/Jue-Xu/Lean-BCH))** — ✅ Complete (0 sorry's before Suzuki extension).
  Proved: `exp_bch`, `norm_bch_sub_add_sub_bracket_le` (H1), `norm_symmetric_bch_sub_add_le` (H2), Lie bracket bridge (M1).

- [ ] **General Suzuki hierarchy (H2)** — Prove convergence of the $2k$-th order Suzuki formula $S_{2k}$ defined recursively:
  $$S_{2k}(t) = S_{2k-2}(p_k t)^2\, S_{2k-2}((1-4p_k)t)\, S_{2k-2}(p_k t)^2, \quad p_k = \frac{1}{4-4^{1/(2k-1)}}$$
  This gives O(1/n^{2k}) convergence. Very ambitious — requires induction on the Suzuki order $k$ and tracking error cancellation at each level. Likely a separate project.

- [x] **Commutator-scaling Trotter error (H)** — Proved `norm_lie_trotter_comm_scaling`: for `t ≥ 0`, the Trotter error `‖exp(tB)exp(tA) - exp(t(A+B))‖` is bounded by `‖[B,A]‖/2 · t² · exp(t(‖A‖+3‖B‖))`, replacing the product `‖A‖‖B‖` with the commutator `‖[B,A]‖`. Uses Duhamel formula via FTC-2. File: `LieTrotter/CommutatorScaling.lean`.

- [x] **Tighten commutator-scaling constant to t²/2** — ✅ Done. Used `norm_integral_le_of_norm_le` (non-constant) + FTC-2 on `x²/2` to evaluate `∫₀ᵗ τ dτ = t²/2`.

- [x] **Multi-operator commutator-scaling** — ✅ Done. `LieTrotter/MultiCommutatorScaling.lean` defines `listCommNorm` (sum of commutator norms with suffix sums) and proves `norm_list_prod_exp_sub_exp_sum_comm`. Matches the Proposition in Childs et al. §VII.A for first-order.

- [x] **Second-order (Strang) commutator-scaling** — ✅ Done. Files: `LieTrotter/StrangCommutatorScaling.lean` and `LieTrotter/MultiStrangCommutatorScaling.lean`. Proved Childs et al.'s arXiv Proposition 16:
  $$\|S_2(t) - e^{tH}\| \le \frac{t^3}{12}\|[B,[B,A]]\| + \frac{t^3}{24}\|[A,[A,B]]\|$$
  for anti-Hermitian operators in C*-algebras. Multi-operator version via `palindromicProd` and `listDoubleCommNorm` (induction on operator list).

- [x] **Matrix specialization (F1)** — Complete in `LieTrotter/MatrixCorollaries.lean`, including Lie–Trotter, Strang, Suzuki total error, and state-error corollaries for `Matrix (Fin d) (Fin d) ℂ`.

## Low priority

## Publication / dissemination

- [ ] **Zulip announcement + arXiv submission** — Post to `#general` on [leanprover.zulipchat.com](https://leanprover.zulipchat.com/) and submit the current 35-page manuscript with the public repository link.

- [ ] **ITP/CPP formalization pearl** (medium effort, peer-reviewed) — 2–4 page short paper covering: (1) the algebraic factorization trick for C1 vs. the standard BCH approach, (2) the commutator cancellation for the cubic Strang bound, (3) the Mathlib API gap (`norm_exp_le` for general Banach algebras). Check submission deadlines.

- [ ] **Companion citation for physics papers** — If writing a paper on Hamiltonian simulation or Trotter error bounds, cite this repo as mechanically verified. The O(1/n²) Strang result is directly relevant to quantum simulation.

## Code cleanup

- [ ] **Clean up lint warnings** — The `mathlib: repository has local changes` warning appears because `lake update` modified the local Mathlib checkout. Running `lake update` fresh in a clean clone resolves this. Not a real issue but worth noting for CI.

- [ ] **Remove `import Mathlib.Tactic`** — Replace with specific tactic imports (`Mathlib.Tactic.NoncommRing`, `Mathlib.Tactic.Positivity`, etc.) in `Telescoping.lean` and `ExpBounds.lean` for faster compilation.
