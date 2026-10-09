# Claim-by-claim formal scope

| Paper component | Lean evidence | Status |
|---|---|---|
| Falling recursion, split, zero support, nonnegativity, monotonicity | `Falling.lean` | Proved |
| Quadratic converse, gap form and product-step identity | `Falling.lean` | Proved |
| Full product-ratio induction | `product_ratio_bound` | Proved |
| Interior endpoint, including gaps 2 and 3 | `interior_endpoint` | Proved |
| Actual symmetric-secant bound | `midpointParts_identity`, `midpointParts_monotone`, `symmetric_secant_int` | Proved by exact even/odd product recurrence |
| Axes, large indices and zero-support cases | `falling_add_le_mul`, `paired_large_left`, `quadratic_implies_paired` | Proved |
| Complete paired-factorial classification / Lemma 3 | `paired_classification : PairedClassificationTarget` | Proved under unchanged definitions |
| Literal statement comparison | `TwoBinChallenge.release_matches_literal_statement` | Proved; not independently human-audited |
| Binomial conversion / Corollary 4 | `binomial_factorial_bridge`, `paired_binomial_shift` | Proved including all vanishing cases |
| Pascal window difference / equation (11) | `rankingSurvivalFormula_step` | Proved |
| Singleton monotonicity and endpoint | `rankingSurvivalFormula_monotone`, `pure_singleton_endpoint` | Proved |
| Comparison of the explicit binomial survival formulas | `survivalFormula_dominance` | Proved |
| Literal RV/RK process | Original `SourceModel.lean` | Definitions unchanged |
| Fair coin sample-space size and word length | `coinWords_length`, `coinWords_mem_length` | Proved |
| Arrival-order total count and word length | `arrivalOrders_length`, `arrivalOrders_mem_length` | Proved: n! entries, including repeated degrees |
| Uniform labeled-permutation law and per-arrangement multiplicities | Total n! count is proved; a bijection/counting correspondence is still needed | Open |
| Fixed-order dominance implies random-order dominance | `fixedDominance_implies_randomOrderDominance` | Proved for the actual source count definitions |
| Actual and unconstrained no-saturation events agree | `run_unsaturated_iff`, `sourceSurvivalCount_eq_free` | Proved for arbitrary finite event lists, including zeros |
| First-saturation index, truncation and no-saturation event | `firstSaturationIndex_none_iff`, `firstSaturationIndex_bounds`, `truncatedFirstSaturation_le_length`, `sourceSurvivalCount_eq_no_saturation` | Proved |
| Source no-saturation counts equal binomial formulas | No universal counting bridge yet | Open; 2,904 finite comparisons pass |
| Future-coin independence, common continuation distribution, no rejection through first saturation | No complete source-model theorem yet | Open |
| Actual summation-by-parts identity and fixed-order sufficiency | `tail_comparison_from_identity` still assumes the identity | Open |
| Witness polynomial signs and denominator positivity | `Witness.lean` | Proved algebraic expressions |
| Witness expressions equal actual fixed/random-order source gaps | No universal source-count bridge yet | Open |
| Theorem 1 / all capacities and words | `FullClassificationTarget` remains only a target definition | Open |
| Theorem 2 / universal regimes | No assembly theorem | Open |
| Independent human statement audit | None | Not performed |

Phase B of the handoff is complete. The analytic binomial/window part of C and structural source-model parts of C-E are complete. The full matching classification has not been formalized. No theorem statement or source-model definition was weakened to obtain these results.
