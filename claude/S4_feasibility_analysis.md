# Feasibility Analysis: S₄ Commutator-Scaling via Duhamel

## Status (updated 2026-04-16)

**Completed:**
- HigherCommutator.lean (triple FTC, 0 sorry's) — building block
- StrangCommutatorScalingTight.lean (norm-of-difference Strang bound, 0 sorry's) — NEW RESULT

**Next steps (Task L):**
1. Optimize within Childs' framework: try different split points / term groupings for S₄
2. Extend norm-of-difference to S₄: bound ‖E₅‖ instead of Σ|αₖ|‖Cₖ‖

**Key insight from Strang work:** Childs' S₄ prefactors (Prop 7) are "heuristic" — not proven tight. The balanced factoring choice and term grouping are optimization variables. Our norm-of-difference approach changes the STRUCTURE of the bound (fewer terms, captures cancellation), not just the coefficients.

---

## Setup

S₄(τ) = S₂(pτ)·S₂(pτ)·S₂(qτ)·S₂(pτ)·S₂(pτ), where p = 1/(4-4^{1/3}), q = 1-4p.

As 11 exponentials:  
S₄(τ) = e^{a₁τA}·e^{b₁τB}·e^{a₂τA}·e^{b₂τB}·e^{a₃τA}·e^{b₃τB}·e^{a₄τA}·e^{b₄τB}·e^{a₅τA}·e^{b₅τB}·e^{a₆τA}

with a₁=a₆=p/2, b₁=b₂=b₄=b₅=p, a₂=a₅=p, a₃=a₄=(1-3p)/2, b₃=q.

## Approach 1: Composition of S₂ errors (telescoping)

S₄(τ) - e^{τH} = Σⱼ₌₁⁵ (∏ᵢ<ⱼ S₂(cᵢτ)) · (S₂(cⱼτ) - e^{cⱼτH}) · (∏ᵢ>ⱼ e^{cᵢτH})

Each S₂(cⱼτ) - e^{cⱼτH} has leading order ~ cⱼ³τ³·D₂ from the Strang commutator-scaling bound.

### Why O(τ⁵) fails with this approach

The Suzuki condition gives 4p³ + q³ = 0 (signed). But the telescoping has **position-dependent flanking factors**:

‖S₄ - e^H‖ ≤ Σⱼ ‖left_j‖ · ‖S₂(cⱼτ) - e^{cⱼτH}‖ · ‖right_j‖

For anti-Hermitian operators (‖left_j‖ = ‖right_j‖ = 1):

‖S₄ - e^H‖ ≤ Σⱼ D · |cⱼ|³ · τ³ = D · (4|p|³ + |q|³) · τ³

Since q < 0, we have |q|³ = (-q)³ ≠ q³, so:

4|p|³ + |q|³ = 4p³ + (-q)³ = 4p³ - q³ ≠ 4p³ + q³ = 0

**The triangle inequality destroys the signed cancellation.** Even without the triangle inequality, the signed cancellation Σⱼ cⱼ³·D₂ = 0 only works if D₂ is multiplied by the **same flanking factors** for each j. But left_j and right_j differ for each j, so:

Σⱼ (left_j) · cⱼ³τ³ · D₂ · (right_j) ≠ 0 in general

**Conclusion: The composition approach gives O(τ³) with commutator scaling, NOT O(τ⁵).**

### What the O(τ³) composition bound gives

‖S₄(τ) - e^{τH}‖ ≤ (‖[B,[B,A]]‖/12 + ‖[A,[A,B]]‖/24) · κ · τ³

where κ = 4p³ + |q|³ = 8/(4-4^{1/3})³ ≈ 0.569.

Numerically: p ≈ 0.414, q ≈ -0.657, 4p³ ≈ 0.284, |q|³ ≈ 0.284, sum ≈ 0.569.

This bound uses **commutator norms** but is at **third order** — the same order as a single S₂ step. It's tighter than S₂ only when the double commutator norms are much smaller than ‖A‖²·‖B‖ products.

## Approach 2: Direct Duhamel on 11-exponential product

Define w₄(τ) = e^{-τH}·S₄(τ) and compute w₄'(τ).

This requires the product rule for 12 factors. After simplification:
- The "free" terms (from each exponential's derivative) sum to -H + (Σaᵢ)A + (Σbᵢ)B = -H + H = 0 ✓
- The residual 𝒯₄(τ) involves 10 conjugation terms (one for each "interface" between exponentials)

Each conjugation term can be expanded using the triple FTC to extract nested commutators up to order 3. The order conditions force cancellation of terms O(τ⁰) through O(τ³), leaving O(τ⁴) leading order.

**This IS the approach of Childs et al. (Appendix K), and it gives O(τ⁵).**

### Effort estimate
- 12-factor product rule: ~300 lines (vs ~90 for 4-factor Strang)
- Conjugation expansion to order 3 at each interface: ~200 lines  
- Order-condition cancellation (4 levels): ~150 lines
- Assembly: ~100 lines
- **Total: ~750 lines**

### Can we tighten Childs' coefficients?

Childs et al. use a "balanced factoring" (splitting at the midpoint) to reduce the 12-factor product to two halves. This introduces a heuristic choice. Our direct Duhamel avoids this choice.

However, **the fundamental triangle inequality applications are the same**: after expanding the 10 conjugation terms and canceling lower orders, you still bound ‖Σ remaining terms‖ ≤ Σ ‖terms‖. The coefficients depend on the exact integrals of polynomial expressions in the Suzuki coefficients.

**Honest assessment:** Our approach might give **slightly different** coefficients (because the grouping of terms differs from Childs'), but it's **unlikely to be dramatically tighter**. The main advantage would be:
1. Exact algebraic coefficients (vs Childs' 4-decimal numerical values)
2. Rigorous (non-heuristic) proof
3. Machine-checked correctness

## Approach 3: Hybrid — partial signed tracking

Instead of pure telescoping (loses O(τ⁵)) or full 12-factor Duhamel (750 lines), consider:

Track the **integral representation** (not just the norm) from each S₂ step through the telescoping, but regroup terms to make the cancellation manifest.

Concretely: write S₄(τ) - e^{τH} as a sum of 5 integrals, then show the leading cubic terms cancel by manipulating the integrals algebraically before taking norms.

This requires:
1. The integral representation: S₂(cτ) - e^{cτH} = e^{cτH}·∫₀^{cτ} 𝒯₂(s) ds (anti-Hermitian)
2. Substituting into the telescoping
3. Extracting the leading-order integral and showing its coefficient vanishes

**Challenge:** The flanking factors (∏S₂ and ∏e^{cH}) conjugate each integral differently. To show cancellation, we'd need to show these conjugations don't affect the leading order — which is true to leading order (conjugation by an isometry preserves the O(τ²) structure of 𝒯₂), but the proof is delicate.

**Effort: ~300-400 lines.** More than composition but less than full 12-factor Duhamel.

## Recommendation

### Path A (lower effort, solid result): ~100 lines
Prove the **O(τ³) commutator-scaling bound for S₄** via composition of tight S₂ bounds. New result, uses existing infrastructure. Not as strong as Childs' O(τ⁵) but uses commutator norms instead of product norms.

**Theorem:** ‖S₄(t) - e^{tH}‖ ≤ (‖[B,[B,A]]‖/12 + ‖[A,[A,B]]‖/24) · 0.569 · t³

### Path B (medium effort, publishable): ~400 lines  
The hybrid approach: track signed integrals through telescoping, prove O(τ⁵) with commutator scaling using the cancellation 4p³+q³=0 at the integral level.

### Path C (high effort, comprehensive): ~750 lines
Full 12-factor Duhamel following Childs' strategy, with exact algebraic coefficients.

### Summary table

| Approach | Order | Commutator? | Lines | Novel? |
|----------|-------|-------------|-------|--------|
| Composition (Path A) | O(t³) | Yes (double comm) | ~100 | Yes (new form) |
| Hybrid (Path B) | O(t⁵) | Yes (double comm for leading, quadruple for remainder) | ~400 | Yes (if coefficients differ from Childs) |
| Full Duhamel (Path C) | O(t⁵) | Yes (quadruple comm, 8 terms) | ~750 | Rigorous version of Childs' heuristic |

The triple FTC (already proved, Phase 1) is useful for all three paths.
