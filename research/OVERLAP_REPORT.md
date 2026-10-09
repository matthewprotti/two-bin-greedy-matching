# Prior-work and overlap report

**Search date: 9 October 2026. Bounded public-source investigation; not a novelty clearance.**

## Result being assessed

The precise potential contribution is the necessary-and-sufficient condition `(b-a)^2 <= a+b-2` for universal RV-versus-RANKING stochastic dominance in the specified two-bin random-neighborhood model, separately in both arrival models, together with the paired falling-factorial criterion and explicit excluded-pair witnesses. The result is not merely the existence of unequal-capacity reversals, and is not a proof of the arbitrary-number-of-bins equal-capacity conjecture.

## Direct antecedents inspected

**Nick Arnosti, Greedy Matching in Bipartite Random Graphs.** Stochastic Systems 12(2), 133–150, 2022; online 2021; DOI 10.1287/stsy.2021.0082. The author-hosted April 2021 PDF was read, including Definition 2, Theorem 2, and the conjecture/unequal-capacity footnote on PDF page 5. The published record confirms the model and common-capacity results. That footnote already gives an asymptotic two-bin imbalance where RK does better. Our classification is a more precise question about all capacity pairs and workloads; do not claim to have first observed reversal.

Sources:
- https://nickarnosti.com/ResearchPapers/Arnosti_GreedyMatching.pdf
- https://doi.org/10.1287/stsy.2021.0082
- https://experts.umn.edu/en/publications/greedy-matching-in-bipartite-random-graphs/

**MathIsEvenEasier, Random choice versus a common ranking in equal-capacity bipartite matching.** Dated 6 October; exposition revised 9 October. Pinned `research-note.tex` revision: `147b8fecb94669e0543b9f654a61dec1cb5f79f0`, commit message “Clarify the conditional comparison and bin terminology.” The source still expressly excludes unequal capacities. Its “shared two-bin calculation” is a normalized-coefficient monotonicity/convexity lemma, not the paired falling-factorial criterion in our paper. The source theorem is not used as a proof premise. Its existence and successful author-reported formal builds do not imply that we have independently verified that project.

Sources:
- https://github.com/MathIsEvenEasier/greedy-matching-capacity/blob/147b8fecb94669e0543b9f654a61dec1cb5f79f0/research-note.tex
- https://vibemathed.com/problem/arnosti-s-equal-capacity-greedy-matching-conjecture

**Karl Mahlburg and Clifford Smyth, Symmetric polynomials and symmetric mean inequalities.** Electronic Journal of Combinatorics 20(3), P34, 2013. A structural search located its binomial-product inequality (Lemma 3.5) and standard falling-factorial monotonicity argument. These are relevant background for some easy monotonicity steps, but the inspected statement is not our sum-of-two-products criterion or its sharp quadratic hypothesis. This is a lead for specialist checking, not a claimed exhaustive non-equivalence proof.

Source: https://www.combinatorics.org/ojs/index.php/eljc/article/download/v20i3p34/pdf/

## Search coverage

The query log records exact terminology, algorithm-name searches with unequal/heterogeneous capacities, two-bin classification phrases, falling-factorial variants, binomial square-gap expressions, and structural searches around exchangeable/negative-dependence conditions. Separate domain-limited queries targeted arXiv, GitHub, and MathOverflow. Returned relevant primary sources were inspected; irrelevant keyword collisions were not treated as evidence.

No public matching classification was located in this search. This does not establish absence from MathSciNet/zbMATH, all citations, unindexed preprints, seminars, private correspondence, or concurrent work. We did not perform a full citation-graph or equivalence search. Generic algebraic ingredients need not themselves be new for the classification to be a useful contribution.

## Specialist assessment

Novelty and equivalence questions remain suitable for specialist review. No source author has endorsed this classification or cleared its priority.

## VibeMathed eligibility finding

The current methodology requires a precisely stated prior open question, including a requirement that it was posed by someone else before the work. The specific two-bin capacity classification was formulated during this project; we have not identified an external prior statement of that classification problem. Therefore prepare a curator inquiry first. Do not set “posed by Arnosti, 2021” for our exact question, invent years-open, or silently replace the existing equal-capacity entry.

Source: https://vibemathed.com/methodology (accessed 9 October 2026).

## Permitted conclusion

“Complete paper proof with exact reproducibility evidence; no matching classification found in a bounded public-source search. Novelty, priority, and venue/registry eligibility remain subject to specialist and editorial assessment.”
