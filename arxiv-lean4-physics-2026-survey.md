# Recent Lean 4 Papers on arXiv (2026) — Survey for Lean-Trotter

*Compiled April 18, 2026*

## Executive Summary

The Lean 4 formalization landscape has exploded in early 2026. I found **30+ papers** from the last ~4 months using Lean 4 for formal verification, with several directly relevant to the Lean-Trotter project's concerns (normed algebras, analysis, integrals, physics). Three papers stand out as especially relevant:

1. **Formalization of QFT** (Douglas et al., March 2026) — formalizes the free bosonic QFT + Glimm-Jaffe axioms
2. **CHSH Rigidity** (Zhao & Yu, April 2026) — quantum information formalization that found a gap in a published proof
3. **MerLean** (Ren et al., February 2026) — automated LaTeX→Lean 4 pipeline for quantum computation papers

---

## Tier 1: Directly Relevant to Lean-Trotter

### 1. Formalization of QFT — [arXiv:2603.15770](https://arxiv.org/abs/2603.15770)
**Authors:** Douglas, Hoback, Mei, Nissim (Harvard/MIT)

Formalizes the free massive bosonic Euclidean QFT in 4D and proves it satisfies the Glimm-Jaffe (OS) axioms, all in Lean 4 + Mathlib. Now fully axiom-free (initially assumed Minlos' theorem, nuclear Schwartz space, and Goursat's theorem — all since proved or avoided).

**Lessons for Lean-Trotter:**

- **Chose Glimm-Jaffe over Wightman axioms because Mathlib's measure theory is more mature than its operator theory.** This mirrors our design decision #7 (working over `NormedAlgebra ℝ 𝔸` to avoid instance synthesis issues). Pick the formulation that aligns with Mathlib's strengths.
- **AI-assisted workflow:** Used GPT-5, Gemini 2.5, and Claude Code/Opus as coding assistants. Key technique: "backward-chaining" where they asked AI to propose helper lemmas that would unblock a proof, then cross-validated with other models. This is analogous to our sorry-driven development.
- **Fubini lemmas are painful.** They developed multiple custom Fubini lemmas for pulling integrals apart. We faced similar issues with `ContinuousLinearMap.intervalIntegral_comp_comm` (design decision #8). Their experience confirms this is a general pain point in Lean analysis.
- **Covariance singularities required switching to Bessel function representation** to ensure absolute integrability. Parallels our design decision #1 (choosing the clean algebraic factorization for the step error bound).
- **Complexity management:** Used `DependencyExtractor` tools and auxiliary documentation files (summaries, plans, remaining axioms). Our CLAUDE.md + CHANGELOG.md serves a similar purpose.
- **AI limitations noted:** Context limits prevent AI from decomposing long proofs; AI relies on potentially stale docstrings for Mathlib API. Both issues we've encountered.

### 2. Formalizing CHSH Rigidity — [arXiv:2604.03884](https://arxiv.org/abs/2604.03884)
**Authors:** Zhao, Yu (quantum-ph)

Formalizes the CHSH rigidity theorem (near-optimal CHSH ⟹ locally isometric to canonical qubit strategy) in Lean 4. **Found a gap in the published argument of McKague, Yang, and Scarani (2012).**

**Lessons for Lean-Trotter:**

- **Formalization catches real bugs.** This is the strongest argument for what we're doing — their Lean formalization identified a gap in a 14-year-old paper. Our Lean-Trotter project similarly forces every step to be explicit, which is how we discovered the `NormOneClass` requirement and the `include 𝕂 in` pattern.
- **Quantum information + Lean 4 is happening.** Our project sits at this intersection. This validates the approach of formalizing quantum-adjacent results.

### 3. MerLean: Autoformalization for Quantum Computation — [arXiv:2602.16554](https://arxiv.org/abs/2602.16554)
**Authors:** Ren, Li, Qi (MIT/Northeastern)

Fully automated LaTeX → Lean 4 pipeline. Tested on 3 quantum computing papers, producing 2,050 Lean declarations from 114 statements. End-to-end formalization with bidirectional translation (also Lean→LaTeX for human review).

**Lessons for Lean-Trotter:**

- **The Lean-Trotter project could be a target for MerLean-like tools.** If we ever write up the paper, the existing Lean formalization provides ground truth for evaluating autoformalization systems.
- **Verification burden reduces to new definitions and axioms** — once the core library is formalized, subsequent results are easier. This matches our experience: after Tasks A-D, Assembly (Task E) was straightforward.
- **High-quality (natural language, formal code) pairs are valuable training data.** Our project's detailed CLAUDE.md mapping math ↔ Lean names could contribute to this.

### 4. Isoperimetric Inequality — [arXiv:2603.14663](https://arxiv.org/abs/2603.14663)
**Author:** Samarakkody

Formalizes the classical isoperimetric inequality via Hurwitz's Fourier-analytic proof. Includes Fourier orthogonality, Parseval's theorem, Wirtinger's inequality, and integration by parts.

**Lessons for Lean-Trotter:**

- **Interchange of infinite sums and integrals is a major challenge.** We faced exactly this in Tasks B1-B4 (exp series bounds). Their experience with term-by-term differentiation of Fourier series parallels our `tsum`/`exp` manipulation.
- **Indexing convention mismatches in Mathlib.** Different parts of Mathlib use different conventions for series indices. We hit this with `tsum_eq_zero_add` (shifting indices by 1 or 2).
- **Arc-length reparametrization required custom infrastructure.** Domain-specific setup work is unavoidable — parallels our custom `exp_tsum_form` interface.

---

## Tier 2: Relevant Techniques and Patterns

### 5. Automated Tactics for Polynomial Reasoning — [arXiv:2604.13514](https://arxiv.org/abs/2604.13514)
**Authors:** Shen, Guo, Liu, Zhi

Certificate-based approach: external CAS (SageMath/SymPy) computes Gröbner bases, Lean verifies the certificate.

**Lesson:** For our Module 4b order-condition cancellations (4p³+q³=0), a certificate-based approach with external computation could bypass the pain of doing polynomial arithmetic natively in Lean. We already proved `suzuki4_cubic_cancel` directly, but for more complex order conditions this pattern could help.

### 6. Wu-Ritt Characteristic Sets — [arXiv:2604.14912](https://arxiv.org/abs/2604.14912)
**Authors:** Xiao, Shen, Guo, Wang, Zhi

Formalizes Wu-Ritt method for triangular decomposition with termination and correctness proofs.

**Lesson:** Their approach to proving algorithm termination via well-ordering principles could inform any future computational aspects of our project (e.g., if we wanted to compute explicit Suzuki coefficients within Lean).

### 7. Global Attractors for Actor-Critic Dynamics — [arXiv:2604.13259](https://arxiv.org/abs/2604.13259)
**Author:** Prytula

Formalizes dynamical systems results (compact global attractors, Lipschitz invariant-law maps, fast-slow reduction) in Lean 4.

**Lesson:** This is pure analysis formalization — dynamical systems, Lipschitz continuity, convergence. The techniques for handling Lipschitz maps and convergence arguments likely overlap with our needs in the CommutatorScaling track.

### 8. Ramanujan-Nagell Theorem — [arXiv:2604.09808](https://arxiv.org/abs/2604.09808)
**Author:** Banwait

Complete formalization including algebraic number theory (ring of integers of Q(√-7), class number, unit group).

**Lesson:** Demonstrates that "bridging the gap between textbook proofs and machine-checked counterparts" requires substantial infrastructure work. Their algebraic number theory infrastructure parallels our custom exp-series interface.

### 9. Compression is All You Need — [arXiv:2603.20396](https://arxiv.org/abs/2603.20396)
**Authors:** Freedman et al.

Analyzes MathLib's dependency graph, finding that unwrapped length grows exponentially with depth while wrapped length is ~constant. Uses PageRank to quantify "mathematical interest."

**Lesson:** Our Lean-Trotter project, with its deep dependency chain (A→B→C→D→E→F→G→H→I→J→K→L), is exactly the kind of hierarchically nested structure they study. The exponential compression from reusing lemmas across tracks is what makes the project tractable.

### 10. Erdős Diameter Conjecture Disproof — [arXiv:2604.15305](https://arxiv.org/abs/2604.15305)
**Author:** Ho (April 16, 2026 — 2 days ago!)

Disproves a long-standing conjecture with a Lean 4 formalized proof.

**Lesson:** Lean 4 is now being used to certify *new mathematical results*, not just formalize textbook material. Our project (especially the tighter Strang bound, Task K, which is a new result) fits this trend.

---

## Tier 3: AI + Lean 4 Ecosystem

### 11. SFT-GRPO Data Overlap for Autoformalization — [arXiv:2604.13515](https://arxiv.org/abs/2604.13515)
Finds that keeping SFT and GRPO training data disjoint yields +10.4pp semantic accuracy for Lean 4 autoformalization. Also reveals that compile-only benchmarking misses 30+pp semantic gaps.

### 12. FormalProofBench — [arXiv:2603.26996](https://arxiv.org/abs/2603.26996)
Graduate-level math benchmark for Lean 4. Best model achieves 33.5% accuracy. Performance drops rapidly on harder problems.

### 13. Automated Conjecture Resolution — [arXiv:2604.03789](https://arxiv.org/abs/2604.03789)
Rethlas (informal) + Archon (formal) framework. Automatically resolves an open problem in commutative algebra with Lean 4 verification.

### 14. Nazrin: GNN for Theorem Proving — [arXiv:2602.18767](https://arxiv.org/abs/2602.18767)
Introduces "atomic tactics" — a small finite set sufficient to prove any provable Lean statement. Graph neural network prover that runs on consumer hardware.

### 15. VeriSoftBench — [arXiv:2602.18307](https://arxiv.org/abs/2602.18307)
Shows Mathlib-tuned provers transfer poorly to repository-centric settings. Success correlates with transitive dependency depth.

**Lesson for us:** Our project has deep multi-hop dependencies. AI provers trained on Mathlib alone would likely struggle with our later modules (StrangCommutatorScaling, Suzuki4) because they depend heavily on our own earlier lemmas.

---

## Key Takeaways for Lean-Trotter

### What's changed since we started

1. **Physics formalization in Lean 4 is no longer niche.** The QFT paper (Douglas et al.) is a landmark — it's the first complete formalization of an axiomatic QFT result. CHSH rigidity, quantum error correction codes, and MerLean all confirm that quantum/physics + Lean 4 is a growing community.

2. **AI assistance is now standard.** Every major 2026 formalization paper mentions AI tools (Claude, GPT, Gemini, Copilot). The QFT paper's "backward-chaining with helper lemmas" technique is essentially what we do with sorry-driven development + agent delegation.

3. **Lean 4 is being used for *new* results, not just formalization of known math.** Our tighter Strang bound (Task K) and the S₄ commutator-scaling work (Task L) fit this trend perfectly.

### What we could adopt

1. **Certificate-based tactics for polynomial identities.** The Gröbner basis paper shows how to offload polynomial computation to external CAS and verify in Lean. Could help with Module 4b order conditions.

2. **Cross-model validation for helper lemmas.** The QFT team's approach of proposing helper lemmas with one model and validating with another could reduce dead-end exploration in our S₄ work.

3. **Bidirectional translation (MerLean-style).** When we write up the paper, having a Lean→LaTeX pipeline would help generate the formal appendix automatically.

### What validates our approach

1. **Sorry-driven development is now mainstream.** Multiple papers describe exactly this workflow.
2. **Custom Mathlib interfaces are unavoidable.** Every physics formalization builds substantial custom infrastructure on top of Mathlib. Our `exp_tsum_form`, conjugation FTC lemmas, etc. are par for the course.
3. **Working over ℝ (not general 𝕂) for analysis is the right call.** The QFT paper similarly chose its axiomatic framework to align with Mathlib's strengths.
4. **Detailed documentation pays off.** Our CLAUDE.md is unusually thorough compared to most projects, and this is exactly what the QFT team recommends for managing complexity.

---

## Papers Not Found

No 2026 papers specifically formalize product formulas, Trotter-Suzuki methods, or operator splitting in Lean 4. The Lean-Trotter project appears to be **the first** Lean 4 formalization of these results. The closest work is the physics-side papers on commutator scaling (Childs et al. style) which we cite but none of those have been formalized.
