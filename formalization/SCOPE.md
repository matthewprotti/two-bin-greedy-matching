# Claim-by-claim formal scope

| Paper component | Lean evidence | Status |
|---|---|---|
| Falling recursion, split, zero support, nonnegativity, monotonicity | `Falling.lean` | Proved |
| Product-ratio induction and interior endpoint | `product_ratio_bound`, `interior_endpoint` | Proved, including gaps 2 and 3 |
| Symmetric-secant comparison | `midpointParts_identity`, `midpointParts_monotone`, `symmetric_secant_int` | Proved by exact product recurrence |
| Paired-factorial classification / Lemma 3 | `paired_classification` | Proved under original definitions |
| Binomial conversion / Corollary 4 | `binomial_factorial_bridge`, `paired_binomial_shift` | Proved including vanishing cases |
| Pascal difference / equation (11), monotonicity, endpoint | `rankingSurvivalFormula_step`, `rankingSurvivalFormula_monotone`, `pure_singleton_endpoint` | Proved |
| Survival-formula comparison | `survivalFormula_dominance` | Proved |
| Literal RV/RK process and capacity criterion | Original `Definitions.lean`, `SourceModel.lean`; `MODEL_LOCK.json` | Unchanged from original publication |
| Coin counts, arrival count, fixed-to-random implication | `SourceBridge.lean` | Proved |
| Actual/unconstrained no-saturation equivalence and stopping index | `run_unsaturated_iff`, `sourceSurvivalCount_eq_free`, `firstSaturationIndex_bounds` | Proved |
| Actual source probabilities equal binomial formulas | `freeFirstMass_binomial`, `survivalProbability_binomial`, `rv_survival_formula`, `ranking_survival_formula` | Proved universally |
| Actual matching tails equal recursive finite expectations | `tailKernel_source`, `tailKernel_rvCount`, `tailKernel_rkCount` | Proved |
| Common continuation after saturation and monotone gains | `tailKernel_saturated`, `Continuation.lean` | Proved from the process |
| Actual finite tail identity and fixed-order sufficiency | `source_tail_expansion`, `fixed_sufficiency`, `capacityRegion_implies_fixed` | Proved without assuming the identity |
| Uniform labeled arrival distribution and repeated-degree multiplicity | `arrivalOrders_labeled_indices`, `labeled_arrival_orders_nodup`, `Insertion.lean` | Proved |
| Fixed witness / equation (17) | `fixedWitness_closed_formula`, `fixedWitness_gap_negative` | Proved for actual source probabilities |
| Random witness / finite sum and equation (23) | `uniformWitness_gap`, `uniformWitness_closed_formula`, `uniformWitness_gap_negative` | Proved with labeled weighting and positive denominators |
| Theorem 1: both arrival models | `full_classification : FullClassificationTarget` | Proved |
| Reverse dominance and equality iff statements | `fixed_reverse_classification`, `random_reverse_classification`, `fixed_equality_classification`, `random_equality_classification` | Proved |
| Theorem 2: all four regimes, including strict examples | `four_regimes : FourRegimeTarget` | Proved |
| Literal expanded release statements | `TwoBinChallenge.release_matches_full_statement`, `TwoBinChallenge.regimes_match_literal_statement` | Proved in project-authored challenge files |
| Independent human statement correspondence audit | None | Not performed |
| Novelty/priority and peer review | Bounded prior-work search only | Not established |

The full classification and regimes are complete in Lean as of 10 October 2026. No original target or process definition was weakened. The historical handoff's proof obligations are discharged by the exact finite-expectation development; no additional mathematical hypothesis substitutes for a missing bridge. The audit covers 272 named theorems and seven deliberately false controls. Formal theorem checking is distinct from independent judgment that the model captures the intended research question.
