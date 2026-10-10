---
title: "A sharp capacity criterion for stochastic dominance in two-bin greedy matching"
author: "Matthew Protti · Independent Researcher"
date: "9 October 2026 · Unrefereed manuscript"
---

## Abstract

Consider two bins with positive integer capacities $a\le b$ and jobs with prescribed degrees in $\{0,1,2\}$. Singleton neighborhoods are independent and uniform. RANDOM-VERTEX uses fresh uniform choices among available neighbors, whereas RANKING uses one independently uniform shared bin priority. We prove that RANDOM-VERTEX stochastically dominates RANKING for every finite prescribed degree word if and only if $(b-a)^2\le a+b-2$. The same necessary-and-sufficient condition holds when arrivals are uniformly randomized and the comparison is required for every degree multiset. A paired falling-factorial inequality proves sufficiency; each excluded capacity pair admits a strict reversal with only two flexible jobs, both in an explicit fixed order and under uniform random arrivals. We also classify universal equality, reverse dominance, and mutual non-dominance. The argument is elementary and self-contained.

## Introduction

Randomized greedy matching rules can be compared either on adversarially chosen graphs or after averaging a specified random graph model. These are different questions. Arnosti \cite{Arnosti2022} studies independent uniform neighborhoods of prescribed sizes. His Theorem 2 establishes equality between RANDOM-VERTEX and RANKING at common capacity one and stochastic dominance of RANDOM-VERTEX at common capacity two. He conjectures the corresponding comparison at larger common capacities. His footnote following that conjecture already exhibits an unequal-capacity asymptotic regime in which RANKING performs better. Thus unequal-capacity reversals themselves are not a contribution claimed here.

A recent manuscript by MathIsEvenEasier \cite{MathIsEvenEasier2026} claims the common-capacity comparison for arbitrary numbers of bins and explicitly excludes unequal capacities. Its proof is not an input to this paper. We investigate the two-bin random-neighborhood model with arbitrary positive integer capacities and a uniformly random shared priority. We determine exactly which capacity pairs admit universal stochastic dominance, and prove the same classification separately under uniform random arrivals.

The main criterion is $(b-a)^2\le a+b-2$. A paired falling-factorial inequality supplies the sufficiency argument. A common continuation law reduces the stochastic comparison to first-saturation probabilities. For every excluded pair, a workload with just two flexible jobs yields a strict reversal, including after independently randomizing the arrival order. We also determine the equality and reverse-dominance regimes. The contribution is this capacity classification in the stated model, not a resolution of Arnosti's unrestricted equal-capacity conjecture or a worst-case approximation guarantee.

## Model and classification

Two labeled bins have capacities $a,b$, with $1 \le  a \le  b$. Each job has a prescribed degree in $\{0,1,2\}$. A degree-one job chooses its sole neighbor independently and uniformly between the bins. Degree-two jobs see both bins. A degree-zero job sees neither.

Fix any finite arrival order independently of the neighborhoods and all algorithmic randomness. RV chooses uniformly among available feasible bins, using fresh independent randomness. RK samples one of the two bin-priority orders uniformly and independently at the outset, and always chooses the first available feasible bin in that order. A job with no available neighbor is rejected. Let $M_{\mathrm{RV}},M_{\mathrm{RK}}$ be the numbers accepted.

Delete degree-zero jobs: they affect neither loads nor the number accepted. In the random-order model, deleting them leaves a uniform order on the positive-degree jobs.

Set

\[
r=a-1,\qquad q=b-1,\qquad N=r+q=a+b-2,\qquad d=q-r=b-a,
\]

and write $S=N+2=a+b$ for total capacity.

**Theorem 1 (sharp two-bin classification).** The following are equivalent:

1. $d^2 \le  N$.
2. For every finite positive-degree word and every integer $K$,
   \[
   \Pr(M_{\rm RV}\ge K)\ge\Pr(M_{\rm RK}\ge K).
   \]
3. The same tail comparison holds for every finite degree multiset when its arrivals are independently uniformly randomized.
4. For every possible prefix length and singleton count, RV's first-saturation survival probability is at least RK's.

The probabilities average the random neighborhoods and the algorithms' randomness. This is not a result conditional on an arbitrary fixed graph, for an arbitrary fixed priority order, for biased/correlated singleton neighborhoods, or for adaptive arrivals.

Equivalently, writing capacities as $(a,a+d)$, universal RV dominance holds exactly when

\[
a\ge 1+\frac{d(d-1)}2.
\]

For a given larger gap, this is an exact threshold in the smaller capacity, not a large-capacity approximation.

**Theorem 2 (all universal comparison regimes).** Both for fixed-order universality and for uniform-random-order universality:

| Capacities | Universal conclusion |
|---|---|
| $(1,1)$ or $(1,2)$ | Identical matching-size distributions for every workload. |
| $a=1,b\ge 3$ | RK stochastically dominates RV for every workload, with strict examples. |
| $a\ge 2$ and $(b-a)^2 \le  a+b-2$ | RV stochastically dominates RK for every workload, with strict examples. |
| $a\ge 2$ and $(b-a)^2 > a+b-2$ | Neither algorithm universally dominates the other: there are workloads favoring each. |

“Neither universally dominates” does not assert that every individual workload has crossing distributions.

## A paired falling-factorial inequality

Write

\[
(x)_k=x(x-1)\cdots(x-k+1),\qquad (x)_0=1.
\]

For nonnegative integer $x$, this is zero when $k>x$. Ordinary binomial coefficients are also zero outside their support.

**Lemma 3 (paired falling factorials).** If nonnegative integers $r\le q$ satisfy

\[
(q-r)^2\le r+q,
\]

then for every pair of nonnegative integers $u,v$,

\[
\boxed{(r)_u(q)_v+(q)_u(r)_v\ \ge\ (r)_{u+v}+(q)_{u+v}.}\tag{1}
\]

Conversely, requiring (1) for all $u,v$ forces the capacity condition: the case $u=v=1$ is precisely

\[
2rq\ge r(r-1)+q(q-1)
\quad\Longleftrightarrow\quad (q-r)^2\le r+q.
\]

**Proof.** Put $d=q-r$. If $u=0$ or $v=0$, equality holds. By symmetry in $u,v$, if either is at least $d$, assume $u\ge d$. Then

\[
(r)_u(q)_v\ge (r)_{u+v},\qquad (q)_u(r)_v\ge(q)_{u+v}.
\]

For example, if $u\le q$, the second inequality follows from $q-u\le r$ and monotonicity of integer falling factorials; if $u>q$, its right side is zero. The first is analogous. This also handles $d=0,1$ when $u,v$ are positive.

It remains to consider $d\ge 2$ and $1\le u,v\le d-1$. The premise is

\[
2r\ge d(d-1).\tag{2}
\]

### Product ratio bound

For $0\le u\le d-1$, we have

\[
\frac{(r)_u}{(q)_u}\ge\frac{d-u}{d+u}.\tag{3}
\]

For $u=0$, equality holds. To induct from $j$ to $j+1$, compare

\[
\frac{r-j}{q-j}
\quad\text{with}\quad
\frac{(d-j-1)(d+j)}{(d+j+1)(d-j)}.
\]

All denominators are positive for $0\le j\le d-2$. After clearing them, the difference has numerator

\[
\begin{aligned}
&(r-j)(d+j+1)(d-j)-(q-j)(d-j-1)(d+j)\\
&\hspace{10mm}=d\bigl(2r-d(d-1)+j(j-1)\bigr)\ge0.
\end{aligned}\tag{4}
\]

Here (2) and integer $j\ge 0$ give the sign. Multiplying the induction hypotheses proves (3).

### Symmetric secant bound

Let $F(x)=(x)_v$, now viewed as a real polynomial. We claim

\[
\frac{F(q-u)-F(r)}{d-u}
\le
\frac{F(q)-F(r-u)}{d+u}.\tag{5}
\]

The intervals $[r,q-u]$ and $[r-u,q]$ share midpoint

\[
\mu=\frac{r+q-u}{2}
\]

and have half-widths $(d-u)/2$ and $(d+u)/2$. Their endpoints lie at least at $v-1$: indeed, for integer $d\ge 2$,

\[
r\ge\frac{d(d-1)}2\ge2d-3,
\qquad r-u\ge d-2\ge v-1.
\]

Expand

\[
F(\mu+y)=\prod_{i=0}^{v-1}(\mu-i+y).
\]

All coefficients in this polynomial in $y$ are nonnegative. Its symmetric secant slope is

\[
\frac{F(\mu+h)-F(\mu-h)}{2h}
=\sum_{\ell\ \mathrm{odd}}c_\ell h^{\ell-1},
\]

which is nondecreasing for $h>0$. Comparing the two half-widths proves (5), without invoking any unproved analytic convexity assertion.

### Combining the bounds

The left side minus the right side of (1) equals

\[
(r)_u\bigl[F(q)-F(r-u)\bigr]
-(q)_u\bigl[F(q-u)-F(r)\bigr].\tag{6}
\]

Equation (5) bounds the second bracket by $(d-u)/(d+u)$ times the first; equation (3) supplies the opposite bound for the coefficient ratio. The first bracket is nonnegative, so (6) is nonnegative. This proves the lemma. QED.

**Corollary 4 (paired binomial shift).** Under the same hypotheses, if $u,v\ge 0$ and $s=N-u-v\ge 0$, then

\[
\binom{s}{r-u}+\binom{s}{q-u}
\ge \binom{s}{r}+\binom{s}{q}.\tag{7}
\]

To see this, multiply (1) by the positive number $s!/(r!q!)$. The identity includes all zero-support cases.

## First saturation

Let $\tau$ be the index of the first positive-degree job that fills either bin, or infinity if no such job occurs. Before $\tau$, both bins remain available and every job is accepted.

For a prefix of length $t$ containing $s$ singletons and $f=t-s$ flexibles, let $X_t$ be the number of choices of the capacity-$a$ bin in the unconstrained process, where both bins are regarded as always available. Loads only increase, so

\[
\{\tau>t\}=\{t-q\le X_t\le r\}.\tag{8}
\]

If final unconstrained prefix loads are below both capacities, all earlier loads were also below capacity. Conversely, unconstrained and actual assignments agree through first saturation. This justifies (8) despite the unconstrained definition.

With independent fair binomials $B_j$ and an independent fair Bernoulli $Z$,

\[
X_t^{\rm RV}\sim B_t,\qquad X_t^{\rm RK}\sim B_s+fZ.\tag{9}
\]

Both laws are symmetric about $t/2$. Write $p_s(x)=2^{-s} \operatorname{binom}(s,x)$, with zero masses outside the support. RK's survival probability is

\[
R_t(s)=\frac12\left(
\sum_{x=t-q}^{r}p_s(x)
+\sum_{x=t-r}^{q}p_s(x)
\right).\tag{10}
\]

For instance, reflection changes the branch shifted by $f$ into the second interval in (10).

**Lemma 5.** If $d^2\le N$, then for every $0\le t\le N$, $R_t(s)$ is nondecreasing in integer $s=0,...,t$.

**Proof.** Pascal's identity gives, for $s<t$,

\[
R_t(s+1)-R_t(s)
=\frac14\bigl[p_s(t-q-1)+p_s(t-r-1)-p_s(r)-p_s(q)\bigr].\tag{11}
\]

Set

\[
u=N-t+1\ge1,\qquad v=t-s-1\ge0.
\]

Then $s=N-u-v$, $t-q-1=r-u$, and $t-r-1=q-u$. The bracket in (11) is nonnegative by Corollary 4. QED.

At $s=t$, every choice is an independent fair singleton, so $R_t(t)=\Pr(B_t\in [t-q,r])$, precisely RV's survival probability. Thus

\[
\Pr(\tau_{\rm RV}>t)\ge\Pr(\tau_{\rm RK}>t)\qquad(0\le t\le N).\tag{12}
\]

For $t>N$, survival is impossible: two unfilled bins together hold at most $r+q=N$ accepted jobs. Therefore (12) holds at every prefix.

This proof establishes the entire finite criterion, not merely the last-time inequality. The latter alone is not silently assumed sufficient.

## Common continuation: first saturation controls final matching size

This argument works for arbitrary two positive capacities, without the quadratic condition.

For a word of length $n$, put $L=\min(\tau,n)$. If $L=t<n$, all first $t$ jobs were accepted, one bin has just filled, and the other has exactly $S-t$ spare places, irrespective of which bin filled.

Every subsequent flexible job can use the open bin. Every subsequent singleton independently hits it with probability one half. Conditioning on the prefix, the identity of the full bin, and the ranking does not change the independent future neighborhoods.

Take independent $Y_j$, equal to one for a flexible job and a fair Bernoulli for a singleton, and define

\[
G_t=\min\left(S,\ t+\sum_{j=t+1}^{n}Y_j\right).\tag{13}
\]

For either algorithm, the conditional law of its final matching size given $L=t$ is the law of $G_t$, at every $t$ of positive probability. For $L=n$, all $n$ jobs were accepted; such an event necessarily has $n\le S$, and (13) gives $n$.

Using the same $Y_j$ for all $t$, the untruncated increase from $t$ to $t+1$ is $1-Y_{t+1}\ge 0$. Truncation at $S$ preserves monotonicity. Thus, for every $K$,

\[
h_K(t):=\Pr(G_t\ge K)
\]

is nondecreasing. First-saturation stochastic dominance implies dominance of $L$, and mixing this common increasing function against the two laws gives the claimed final-size stochastic dominance. The empty word is deterministic.

Together with the first-saturation argument, this proves $(1) \Rightarrow  (4) \Rightarrow  (2)$ in Theorem 1. Averaging independent fixed-order inequalities proves $(2) \Rightarrow  (3)$.

For later use, finite summation by parts gives

\[
\Pr(M_{\rm RV}\ge K)-\Pr(M_{\rm RK}\ge K)
=
\sum_{t=0}^{n-1}\Delta_t\,[h_K(t+1)-h_K(t)],\tag{14}
\]

where $\Delta_t=\Pr(\tau_{\mathrm{RV}}>t)-\Pr(\tau_{\mathrm{RK}}>t)$ for that word. This identity follows by writing $h_K(L)=h_K(0)+\sum_{t<L}(h_K(t+1)-h_K(t))$ and taking expectations. It does not require a pathwise coupling of the original processes.

## Every excluded capacity pair has an explicit fixed-order reversal

Suppose $d^2>N$. Then $d\ge 2$ and $N\ge 2$. Consider

\[
\underbrace{1,\ldots,1}_{N-2\ \mathrm{singletons}},\quad 2,2,1.\tag{15}
\]

There are $n=N+1=S-1$ jobs and exactly two flexibles. Through time $N-1$, every prefix has at most one flexible, so the two unconstrained laws in (9), and hence their survival probabilities, coincide.

At time $N$, survival requires $X_N=r$. Set

\[
p=2^{-N}\binom Nr>0.
\]

RV's survival probability is $p$; RK's is

\[
2^{-(N-1)}\left[\binom{N-2}{r}+\binom{N-2}{q}\right].
\]

Using $r+q=N$ and $(q-r)^2=d^2$ gives

\[
\Delta_N=p\,\frac{N-d^2}{N(N-1)}.\tag{16}
\]

Only the final singleton can distinguish the common continuation kernels at these two last times for the all-matched threshold $K=n$. Equation (14) therefore yields

\[
\boxed{
\Pr(M_{\rm RV}=N+1)-\Pr(M_{\rm RK}=N+1)
=
\frac{\binom Nr}{2^N}\frac{N-d^2}{2N(N-1)}<0.
}\tag{17}
\]

In fact every other tail is equal for this particular fixed word, because $G_N$ takes only the values $N,N+1$. Earlier singleton rejections are not ignored: their identical contributions cancel in (14).

This proves necessity for fixed-order universality and for the finite first-saturation criterion. Merely observing a negative survival inequality was not enough; (15)--(17) provide the full matching counterexample.

## The same excluded pairs fail under uniform random arrival order

Necessity for uniform random arrivals does not follow by averaging one fixed-order reversal. It needs its own argument.

Use the same multiset: two flexibles and $N-1=S-3$ singletons, with $n=N+1$ jobs in independent uniform random order. The two flexible positions form a uniform two-element subset of $\{1,\ldots,n\}$.

For a prefix of length $t$ containing both flexibles, let

\[
A_t=\binom{t-2}{r-1}+\binom{t-2}{q-1}
    -\binom{t-2}{r}-\binom{t-2}{q}.\tag{18}
\]

Expanding the two flexible-choice factors gives

\[
\Delta_t=2^{-t}A_t,\qquad 2\le t\le N.\tag{19}
\]

If at most one flexible has arrived, $\Delta_t=0$. Once both have arrived, the remaining jobs are all singletons, so at threshold $K=n$,

\[
h_n(t+1)-h_n(t)=2^{-(n-t)}.
\]

The probability both flexibles occur among the first $t$ positions is $\operatorname{binom}(t,2)/\operatorname{binom}(n,2)$. Averaging (14) yields the exact formula

\[
\Delta^{\rm unif}_{n}
=
\frac{1}{2^n\binom n2}
\sum_{t=2}^{n-1}\binom t2 A_t.\tag{20}
\]

There is no independence assumption between the saturation event and flexible positions here: the fixed-word identity is averaged over all position pairs.

To sum (20), use

\[
\sum_{t=2}^{n-1}\binom t2\binom{t-2}{k}
=
\binom{k+2}{2}\binom n{k+3}\tag{21}
\]

for integer $k\ge 0$, by the binomial multiplication identity followed by the hockey-stick identity. For $k=-1$, both sides are zero under the convention $\operatorname{binom}(1,2)=0$.

Set $z=d^2$ and

\[
\begin{aligned}
P_N(z)
&=z^2-(N^2+9N+26)z+N^3+10N^2+24N\\
&=(z-N-2)(z-N^2)-8(N+3)(z-N),\\
D_N(z)&=((N+4)^2-z)((N+6)^2-z).
\end{aligned}\tag{22}
\]

Applying (21) to the four terms in (18), substituting $n=N+1$, and cancelling factorials gives

\[
\boxed{
\Delta^{\rm unif}_{n}
=
\frac{\binom Nr}{2^N}
\frac{2(N+2)P_N(d^2)}{N D_N(d^2)}.
}\tag{23}
\]

For reproducibility, the unsimplified numerator before the factorial cancellation is

\[
\binom{r+1}{2}\binom{N+1}{r+2}
-\binom{r+2}{2}\binom{N+1}{r+3}
+\binom{q+1}{2}\binom{N+1}{q+2}
-\binom{q+2}{2}\binom{N+1}{q+3}.
\tag{24}
\]

The exact checker compares (20), (23), and full random-order process distributions, rather than relying only on a symbolic simplifier.

Now $d$ and $N$ have the same parity, so $d^2>N$ implies $d^2\ge N+2$. Also $0\le d\le N$, hence $d^2\le N^2$. Consequently the product $(z-N-2)(z-N^2)$ in (22) is nonpositive, and the remaining term $-8(N+3)(z-N)$ is strictly negative. Thus $P_N(d^2)<0$. The denominator in (23) is positive, and so

\[
\Delta^{\rm unif}_{n}<0.
\]

This proves $(3) \Rightarrow  (1)$ and completes Theorem 1 in both arrival models.

## Equality, reverse dominance, and strict examples

### A capacity-one bin

Let $a=1$. For $0\le t\le b-1$, survival requires that every unconstrained choice avoid this bin. Therefore RV survival is $2^{-t}$. RK survival is also $2^{-t}$ if there are no flexibles, and otherwise it is $2^{-(s+1)}$ for $s$ singleton jobs.

Since $t=s+f$ and $f\ge 1$, RK survival is at least RV survival. For $t\ge b$, neither process can remain unsaturated. The common continuation kernel proves universal RK dominance, both for fixed orders and after averaging.

For $b=1,2$, the only potentially nonzero survival comparisons have $t\le 1$, so all comparisons are equal. This proves universal equality for $(1,1),(1,2)$.

For every $b\ge 3$, the fixed word $(2,2,1)$ gives all-matched probabilities $5/8$ under RV and $3/4$ under RK. Uniform random ordering gives $19/24$ and $5/6$. Thus reverse dominance is genuinely strict for some workloads.

### RV has a strict example whenever $a\ge 2$

Take $a$ flexible jobs followed by one singleton. If $b>a$, RV's all-matched probability is $1-2^{-(a+1)}$ and RK's is $3/4$. Their positive difference is

\[
\frac14-2^{-(a+1)}.
\]

If $b=a$, either bin can fill, giving probabilities $1-2^{-a}$ and $1/2$; the difference $1/2-2^{-a}$ is positive for $a\ge 2$.

In an independent uniform order of this multiset, failure is possible only if the singleton is last, with probability $1/(a+1)$. Each fixed-order gap is therefore divided by $a+1$, preserving strict positivity.

Together with the universal results and the excluded-pair witnesses, this proves Theorem 2. In particular, outside the quadratic region and with $a\ge 2$, there are explicit workloads favoring each algorithm even under uniform random arrivals.

## Consequences and interpretation

The earlier adjacent-capacity and gap-two results are special cases. The smallest smaller-bin capacities allowing universal RV dominance for gaps $0,1,2,3,4,5,6$ are respectively

\[
1,1,2,4,7,11,16.
\]

The old finite sufficient first-saturation test is now an exact decision procedure for the universal comparison, but the proof also eliminates the need to run it: one integer inequality decides the capacity pair.

The boundary has a square-root form in total capacity:

\[
b-a\le\sqrt{a+b-2}.
\]

This is an exact statement of the theorem, not a normal approximation. The falling-factorial obstruction already appears in degree two ($u=v=1$); the substantive sufficiency argument shows why controlling that one quadratic expression controls all higher orders.

No mechanism here proves an averaged invariant for three bins. The two-bin continuation reduction depends on exactly one bin remaining open after first saturation. It cannot simply be reused when two or more residual bins remain.



## Verification, attribution, and limitations

The universal results rest on the proofs above. Exact finite calculations are supplied separately as falsification and implementation-cross-checking evidence. The inherited verification suite includes 5,047,120 first-saturation comparisons, 805,980 falling-factorial comparisons, and 112,585 direct-process workload profiles. An independently implemented small sample-space oracle cross-checks a subset of these calculations. The implementations share AI-assisted authorship and do not constitute independent human review. The sealed computational package was replayed successfully during preparation of this manuscript on 9 October 2026.

A supplied positive review of the consolidated proof and replay receipt have unidentified provider provenance. No independent human expert review or journal peer review is established. The historical archives retain their original status labels.

Lean 4.19.0 proves the full matching classification and all four regimes for the original source model, including both witness formulas. All 272 named theorems use only standard logical axioms; seven false controls are rejected. Independent human statement correspondence review remains outstanding.

The question investigated here was formulated during this project as an unequal-capacity extension motivated by the preceding references. A bounded literature search found no matching classification, but novelty and priority have not been cleared with the source authors or domain specialists. No theorem for three or more bins is asserted.

### AI contribution and author responsibility

This is human-directed, substantially AI-developed mathematical work. Matthew Protti selected the research direction, commissioned the successive extensions and reviews, required reproducible evidence and explicit scope boundaries, and directed preparation for publication. OpenAI ChatGPT research sessions identified in the project as GPT-6 Astra Pro generated substantial portions of the constructions, algebraic and probabilistic arguments, verification programs, adversarial checks, and manuscript. OpenAI Codex completed and audited the Lean formalization and cross-checked its executable model. AI systems are tools, not coauthors. Matthew Protti is the responsible human author; release approval is distinct from a claim of independent human reconstruction of every proof step.

\begin{thebibliography}{9}
\bibitem{Arnosti2022}
Nick Arnosti.
\newblock Greedy Matching in Bipartite Random Graphs.
\newblock \emph{Stochastic Systems} \textbf{12}(2), 133--150, 2022; published online 2 November 2021.
\newblock DOI: \href{https://doi.org/10.1287/stsy.2021.0082}{10.1287/stsy.2021.0082}.
\newblock Author's April 2021 version, Theorem 2 and footnote 6, also consulted.

\bibitem{MathIsEvenEasier2026}
MathIsEvenEasier.
\newblock Random choice versus a common ranking in equal-capacity bipartite matching.
\newblock Public research manuscript, 6 October 2026; exposition revised 9 October 2026.
\newblock Repository \texttt{MathIsEvenEasier/greedy-matching-capacity},
\texttt{research-note.tex}, commit
\texttt{147b8fecb94669e0543b9f654a61dec1cb5f79f0}.
\newblock Accessed 9 October 2026. The manuscript's claimed theorem is not assumed here.
\end{thebibliography}
