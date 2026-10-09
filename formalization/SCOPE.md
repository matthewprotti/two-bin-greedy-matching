# Claim-by-claim formal scope

| Paper component | Lean evidence | Status |
|---|---|---|
| Falling-factorial recursion, split, zero support, nonnegativity, monotonicity | `Falling.lean` | Checked |
| Paired inequality implies quadratic condition | `paired_implies_quadratic` | Checked converse only |
| Quadratic condition in gap form; one-step product identity and sign | `gap_form`, `product_step_identity`, `product_step_nonnegative` | Checked |
| Full product-ratio induction | No release theorem | Open |
| Monotonicity of normalized odd-coefficient sum | `oddSlope_monotone` | Checked generic helper |
| Falling polynomial expansion and actual symmetric-secant bound | No bridge from falling factorials to generic helper | Open |
| Combining product/secant bounds | `combine_product_secant` | Checked conditional helper; hypotheses still need proof |
| All cases of paired-factorial sufficiency / Lemma 3 | `PairedClassificationTarget` is only a proposition definition | Open |
| Binomial conversion including all support boundaries / Corollary 4 | No theorem | Open |
| Literal RV/RK process | `SourceModel.lean` defines coin sample space and persistent ranking priority | Defined; finite execution checks only |
| Four small source count equalities | `reversal_*_count`, `adjacent_*_count` | Kernel checked; no axioms |
| First-saturation distribution and binomial windows | No source-model identification theorem | Open |
| Monotone clipped continuation and nonnegative mixtures | `FiniteKernel.lean` | Checked algebraic helpers |
| Actual continuation distribution and summation-by-parts identity | `tail_comparison_from_identity` assumes the identity | Open universal bridge |
| Witness polynomial factorization, sign, denominator positivity | `Witness.lean` | Checked algebraic expressions |
| Fixed-order and random-order witness expressions equal actual process gaps | No universal source-count bridge | Open |
| Labeled random-arrival weighting | Multiplicities retained by definition; finite oracle checks | Universal combinatorial proof open |
| Theorem 1 for all capacities and finite words | `FullClassificationTarget` is only a proposition definition | Open |
| Theorem 2's universal regimes | No assembly theorem | Open |
| Independent informal-to-formal statement audit | None | Not performed |

The handoff's Phase A (build/audit of the supplied supporting source) is completed. Phases B-E are not complete. No theorem statement was weakened to obtain the build. None of the computational receipts certify the missing universal bridges.
