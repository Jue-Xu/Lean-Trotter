# TODO

## Remaining work (as of 2026-04-22)

The project has 0 sorries and 9 axioms (all BCH-interface, in `Suzuki4ViaBCH.lean`).
Main headline results—Lie-Trotter, Strang, commutator scaling, Suzuki S₄ with L1/L3/L4
BCH bounds—are all proved. Remaining work falls into five tracks:

### Track A: Eliminate the 9 BCH-interface axioms (headline gap)

The single largest completion step. All 9 axioms are in `Suzuki4ViaBCH.lean`
and stand in for Lean-BCH theorems + two CAS-derived numerical claims.

| Axiom | What it asserts | Path to eliminate |
|---|---|---|
| `symmetric_bch_cubic` + 3 helpers | Lean-BCH's symmetric BCH cubic | Import Lean-BCH once its `quintic_pure_identity` nsmul-diamond gap (line 2307, ~50 lines fix) closes |
| `bch_iteratedDeriv_s4Func_order4` | BCH ⟹ h4 | Derive from Lean-BCH expansion + Phase 5 bridge |
| `bch_w4Deriv_quintic_level2` | Primitive pointwise residual (unit coefs) | Derive from Lean-BCH + norm bound |
| `bch_w4Deriv_level3_tight` | BCH pointwise with tight γᵢ | Derive: Lean-BCH quintic + γᵢ projection |
| `bch_childs_pointwise_residual` | Childs heuristic residual | Stays axiomatic (encodes Childs's claim directly) |
| `bch_uniform_integrated` | Level 4 uniform bound (R₅ + R₇) | Derive: Lean-BCH quintic + R₇ norm bound |

**Bottleneck:** Lean-BCH's `quintic_pure_identity` nsmul typeclass diamond
(companion project `/Users/jue/Documents/Claude/Projects/Lean-BCH/`). Once
that compiles, imports flow through and most axioms become theorems.

### Track B: h4 alternative (Path A, Lean-native)

As an alternative to Path B (Lean-BCH route), prove `sumQuadCorr (s4DList A B p) = 0`
directly in `Suzuki4MultinomialExpand.lean`. Blocked on `module` tactic timeout
for the quartic expansion (11 cons steps × 16 monomials, 8M heartbeats insufficient).
Approaches:
1. Manual cons-by-cons induction with BCH-like invariant (~1000 lines).
2. Helper tactic / preprocessing to reduce `module` load.
3. CAS-preprocessing: simplify the identity symbolically, import as pre-reduced form.

Either Track A or B suffices; Track A is more promising because Lean-BCH is
~50 lines from completion.

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
- **Track A:** close Lean-BCH's `quintic_pure_identity` gap (`/Users/jue/Documents/Claude/Projects/Lean-BCH/BCH/Basic.lean`, line 2307). ~1-2 sessions.
- Once closed, flip the imports in `Suzuki4ViaBCH.lean`: 9 axioms → 0 or 1 axiom.

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
  - `norm_suzuki4_childs_form_via_bch`: Childs 2021 Prop pf4_bound_2term with
    exact coefficients 0.0047-0.0284.
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
