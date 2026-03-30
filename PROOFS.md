# Mathematical Proofs — Lie-Trotter and Strang Splitting

This document presents the complete proof chain in standard mathematical notation.
All results are formalized in Lean 4 with Mathlib; the corresponding theorem names are given in parentheses.

---

## Setting

Let $\mathfrak{A}$ be a complete normed algebra over $\mathbb{K} \in \{\mathbb{R}, \mathbb{C}\}$ with $\|1\| = 1$.
The exponential is defined by the absolutely convergent power series:

$$e^a = \sum_{k=0}^{\infty} \frac{a^k}{k!}$$

---

## Part I: Exponential Bounds

### Lemma B1 (`norm_exp_le`)

*For any $a \in \mathfrak{A}$:*

$$\|e^a\| \le e^{\|a\|}$$

**Proof.** By the triangle inequality applied to the power series:
$\|e^a\| = \|\sum_{k \ge 0} a^k/k!\| \le \sum_{k \ge 0} \|a\|^k/k! = e^{\|a\|}$. $\square$

### Lemma B2 (`norm_exp_sub_one_le`)

$$\|e^a - 1\| \le e^{\|a\|} - 1$$

**Proof.** $e^a - 1 = \sum_{k \ge 1} a^k/k!$. Take norms: $\le \sum_{k \ge 1} \|a\|^k/k! = e^{\|a\|} - 1$. $\square$

### Lemma B3 (`exp_sub_one_sub_bound_real`)

*For $x \ge 0$:*

$$e^x - 1 - x \le \frac{x^2}{2}\, e^x$$

**Proof.** Write $e^x - 1 - x = \sum_{k \ge 2} x^k/k!$. For $k \ge 2$, $k! \ge 2 \cdot (k-2)!$, so $x^k/k! \le (x^2/2) \cdot x^{k-2}/(k-2)!$. Summing: $\le (x^2/2) \sum_{j \ge 0} x^j/j! = (x^2/2)\, e^x$. $\square$

### Lemma B4 (`norm_exp_sub_one_sub_le`)

$$\|e^a - 1 - a\| \le \frac{\|a\|^2}{2}\, e^{\|a\|}$$

**Proof.** Write $e^a - 1 - a = \sum_{k \ge 2} a^k/k!$. Take norms termwise: $\le \sum_{k \ge 2} \|a\|^k/k! = e^{\|a\|} - 1 - \|a\|$. Apply B3 to $x = \|a\|$. $\square$

### Lemma B5 (`norm_exp_remainder3_le`)

$$\left\|e^a - 1 - a - \tfrac{1}{2}a^2\right\| \le \frac{\|a\|^3}{6}\, e^{\|a\|}$$

**Proof.** Same as B4 but shifted by one more order: $\sum_{k \ge 3} \|a\|^k/k! = e^{\|a\|} - 1 - \|a\| - \|a\|^2/2$, and $k! \ge 6 \cdot (k-3)!$ for $k \ge 3$. $\square$

---

## Part II: Algebraic Identities

### Lemma A1 (`telescoping_direct`)

*For any $X, Y$ in a ring:*

$$X^n - Y^n = \sum_{k=0}^{n-1} X^k (X - Y) Y^{n-1-k}$$

**Proof.** By induction on $n$. Factor out $Y$ from the inner sum to get the inductive step:
$\sum_{k<m} X^k(X-Y)Y^{m-k} = (\sum_{k<m} X^k(X-Y)Y^{m-1-k}) \cdot Y = (X^m - Y^m) \cdot Y$. $\square$

### Lemma A2 (`norm_pow_sub_pow_le'`)

*In a normed ring with $\|1\|=1$, for $M = \max(\|X\|, \|Y\|)$:*

$$\|X^n - Y^n\| \le n \|X - Y\| \cdot M^{n-1}$$

**Proof.** Apply A1, then bound each summand: $\|X^k(X-Y)Y^{n-1-k}\| \le M^k \|X-Y\| M^{n-1-k} = \|X-Y\| M^{n-1}$. Sum over $k = 0, \ldots, n-1$. $\square$

### Lemma D1 (`exp_div_pow`)

*For $n \ge 1$:*

$$(e^{a/n})^n = e^a$$

**Proof.** Since $a/n$ commutes with itself, $e^{a/n} \cdot e^{a/n} = e^{2a/n}$ by the Baker-Campbell-Hausdorff formula for commuting elements. By induction (or directly from `exp_nsmul`): $(e^{a/n})^n = e^{n \cdot a/n} = e^a$. $\square$

---

## Part III: Step Error Bounds

### Lemma C-aux (`norm_pow_add_sub_pow_sub_pow`)

*For $m \ge 1$ in a normed ring:*

$$\|(a+b)^m - a^m - b^m\| \le (\|a\|+\|b\|)^m - \|a\|^m - \|b\|^m$$

**Proof.** By induction on $m$. Base: $m = 1$ gives $0 \le 0$. Step: use the identity

$$(a+b)^{m+1} - a^{m+1} - b^{m+1} = (a+b)\bigl((a+b)^m - a^m - b^m\bigr) + a b^m + b a^m$$

and bound using $\|a+b\| \le \|a\|+\|b\|$, the inductive hypothesis, and submultiplicativity. The real-valued RHS satisfies the same recurrence by `ring`. $\square$

### Lemma C-cross (`norm_exp_cross_term_le`)

$$\|e^{a+b} - e^a - e^b + 1\| \le (e^{\|a\|}-1)(e^{\|b\|}-1)$$

**Proof.** Write $e^{a+b} - e^a - e^b + 1 = \sum_{k \ge 2} \frac{(a+b)^k - a^k - b^k}{k!}$ (the $k=0,1$ terms vanish). Apply C-aux termwise: $\le \sum_{k \ge 2} \frac{(\|a\|+\|b\|)^k - \|a\|^k - \|b\|^k}{k!} = (e^{\|a\|}-1)(e^{\|b\|}-1)$. $\square$

### Theorem C1 (`norm_exp_mul_exp_sub_exp_add'`)

$$\|e^a e^b - e^{a+b}\| \le 2 \|a\| \|b\|\, e^{\|a\|+\|b\|}$$

**Proof.** The algebraic identity (by `ring` in any ring):

$$e^a e^b - e^{a+b} = (e^a - 1)(e^b - 1) - (e^{a+b} - e^a - e^b + 1)$$

Both terms are bounded by $(e^{\|a\|}-1)(e^{\|b\|}-1)$ using B2 and C-cross, giving a total $\le 2(e^{\|a\|}-1)(e^{\|b\|}-1)$.

Then $(e^s - 1)(e^t - 1) \le st\, e^{s+t}$ since $e^s - 1 \le s\, e^s$. $\square$

### Theorem C1-refined (`norm_exp_mul_exp_sub_exp_add_sub_comm_le`)

*The Lie-Trotter error with the commutator extracted:*

$$\left\|e^a e^b - e^{a+b} - \frac{[a,b]}{2}\right\| \le \frac{3}{2} \|a\| \|b\| (\|a\|+\|b\|)\, e^{\|a\|+\|b\|}$$

*where $[a,b] = ab - ba$ is the ring commutator.*

**Proof.** Decompose $E(a,b) = e^a e^b - e^{a+b}$ as $[a,b]/2 + R(a,b)$ where:
- $(e^a-1)(e^b-1) - ab = aF(b) + F(a)b + F(a)F(b)$ with $F(x) = e^x - 1 - x$, giving $O(\|a\|^2\|b\| + \|a\|\|b\|^2)$
- The cross-tail $e^{a+b}-e^a-e^b+1 - \frac{ab+ba}{2}$ is bounded using B5 and the identity $\text{cross}(a,b) - \frac{ab+ba}{2} = R_2(a+b) - R_2(a) - R_2(b)$ where $R_2(z) = e^z - 1 - z - z^2/2$. $\square$

---

## Part IV: First-Order Lie-Trotter

### Theorem E1 (`lie_trotter_error_rate`)

*There exists $C > 0$ such that for all $n \ge 1$:*

$$\left\|(e^{A/n} e^{B/n})^n - e^{A+B}\right\| \le \frac{C}{n}$$

*with $C = 2\|A\|\|B\|\, e^{\|A\|+\|B\|} + 1$.*

**Proof.** Set $P_n = e^{A/n} e^{B/n}$ and $Q_n = e^{(A+B)/n}$.

1. $Q_n^n = e^{A+B}$ by D1.
2. $\|P_n^n - Q_n^n\| \le n \|P_n - Q_n\| \cdot M^{n-1}$ by A2, where $M = \max(\|P_n\|, \|Q_n\|)$.
3. $\|P_n - Q_n\| \le 2\|A\|\|B\|/n^2 \cdot e^{(\|A\|+\|B\|)/n}$ by C1 with $a = A/n$, $b = B/n$.
4. $M \le e^{(\|A\|+\|B\|)/n}$ by B1.
5. Combine: $n \cdot \frac{2\|A\|\|B\|}{n^2} \cdot e^{s/n} \cdot e^{s/n \cdot (n-1)} = \frac{2\|A\|\|B\|}{n} \cdot e^s$ where $s = \|A\|+\|B\|$. $\square$

### Theorem E2 (`lie_trotter`)

$$\lim_{n \to \infty} (e^{A/n} e^{B/n})^n = e^{A+B}$$

**Proof.** Standard $\varepsilon$-$N$ argument using E1: choose $N > C/\varepsilon$. $\square$

---

## Part V: Second-Order Strang Splitting

### Theorem F-cubic (`norm_exp_mul_exp_mul_exp_sub_exp_add_cubic`)

$$\|e^a e^b e^a - e^{2a+b}\| \le C(\|a\|^2 \|b\| + \|a\| \|b\|^2 + \|a\|^3)\, e^{2\|a\|+\|b\|}$$

**Proof.** Factor using the algebraic identity:

$$e^a e^b e^a - e^{2a+b} = \underbrace{e^a \cdot [e^b, e^a]}_{\text{commutator piece}} + \underbrace{e^{2a} e^b - e^{2a+b}}_{\text{standard error } E(2a,b)}$$

where $[X, Y] = XY - YX$ is the ring commutator.

**The cancellation:** Since $a + b = b + a$ (addition is commutative):

$$[e^b, e^a] = E(b,a) - E(a,b) = [e^b - 1, e^a - 1]$$

At leading order, $[e^b-1, e^a-1] \approx [b, a] = -[a, b]$ and $E(2a, b) \approx [a, b]$. These cancel:

$$e^a \cdot (-[a,b]) + [a,b] = (e^a - 1) \cdot (-[a,b]) \approx -a[a,b]$$

which is cubic in $\|a\|, \|b\|$.

The remaining terms (from the commutator remainder and higher-order cross terms) are all bounded using B4, B5, and C-cross. With $a = A/2n$, $b = B/n$, the step error is $O(1/n^3)$. $\square$

### Theorem F-rate (`strang_error_rate_sq`)

*There exists $C > 0$ such that for all $n \ge 1$:*

$$\left\|(e^{A/2n} e^{B/n} e^{A/2n})^n - e^{A+B}\right\| \le \frac{C}{n^2}$$

**Proof.** Same telescoping argument as E1, but with:
- Step error $O(1/n^3)$ from F-cubic (instead of $O(1/n^2)$)
- Uniform bound $\max(\|S_n\|, \|Q_n\|) \le e^{(\|A\|+\|B\|)/n}$ (using B1 applied three times for $\|S_n\|$)
- Assembly: $n \cdot O(1/n^3) \cdot e^s = O(1/n^2)$. $\square$

### Theorem F-main (`symmetric_lie_trotter`)

$$\lim_{n \to \infty} (e^{A/2n} e^{B/n} e^{A/2n})^n = e^{A+B}$$

**Proof.** Standard $\varepsilon$-$N$ argument using F-rate: choose $N > C/\varepsilon$ (sufficient since $C/N^2 \le C/N < \varepsilon$ for $N \ge 1$). $\square$

---

## Dependency Graph

```
B1 ─── B2 ─────────────────────── C1 (quadratic) ────── E1 ───── E2 (Lie-Trotter)
 │      │                          │                     │
B3 ─── B4 ──── C-aux ── C-cross ──┘                     │
 │                                                       │
B5 ──── C1-refined ── F-cubic ──── F-rate ──── F-main (Strang)
                                     │
A1 ── A2 ────────────────────────────┘
       │
D1 ────┘
```

---

## Notation

| Symbol | Meaning |
|--------|---------|
| $\mathfrak{A}$ | Complete normed algebra with $\|1\|=1$ |
| $e^a$ | `NormedSpace.exp a` (Mathlib) |
| $\|a\|$ | Norm in $\mathfrak{A}$ |
| $[a,b]$ | $ab - ba$ (ring commutator) |
| $F(a)$ | $e^a - 1 - a$ (second-order remainder) |
| $R_2(a)$ | $e^a - 1 - a - a^2/2$ (third-order remainder) |
