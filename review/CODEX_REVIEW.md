# Review findings — 9 October 2026

The paper's argument appears internally sound on this review. No counterexample or mathematical error was found. This is an AI-assisted audit, not an independent human specialist endorsement or a novelty clearance.

## Findings and repairs

1. **The Lean build was incomplete in two senses.** It had not been run, and the headline results are only target definitions. The existing supporting library now compiles after a statement-preserving repair to `falling_add`; the full algebraic criterion and the probabilistic bridges remain open. The public labels and manuscript now make this explicit.
2. **The negative-control harness accepted any compilation failure.** Missing imports could have masqueraded as rejection of a false claim. The repaired harness first checks positive counterparts, audits all 27 named theorems, and requires false controls to fail at their intended claims.
3. **The sealed verifier was incompatible with a Git/Lean checkout.** It counted `.git` and `.lake` files as unexpected members and would copy them during replay. The working repository now excludes generated directories while checking every publication file. The original historical archive is unchanged.
4. **VibeMathed fit is not established.** Its [methodology](https://vibemathed.com/methodology), read on 9 October, includes a question posed by someone else before the work. This precise unequal-capacity classification arose within the project. The draft discloses that history and requests editorial assessment; it does not falsely identify Arnosti as having posed this exact question in 2021.

## Mathematical checks

The product-ratio induction, integer endpoint bound (including gaps 2 and 3), zero-support binomial conversion, common continuation law, and separate random-arrival necessity calculation were reviewed. The $(1,1)$ and capacity-one regimes are handled explicitly. Random-order necessity is not inferred merely by averaging one bad fixed order.

The full supplied Python suite reproduced its sealed results: 5,047,120 prefix comparisons, 805,980 falling-factorial comparisons, 112,585 direct process profiles, and the witness checks. The actual Lean source model is additionally compared with the separate historical oracle; inspect the [receipt](../evidence/source-model-check.json) for the finite bounds. Passing these checks is evidence against implementation mistakes, not proof of the missing universal formalization.

## Positioning and recommendation

[Arnosti's paper](https://nickarnosti.com/ResearchPapers/Arnosti_GreedyMatching.pdf), Theorem 2 and footnote 6, already treats the random-neighborhood comparison and gives unequal-capacity reversals. The contribution claimed here is the exact capacity classification. The [pinned equal-capacity manuscript](https://github.com/MathIsEvenEasier/greedy-matching-capacity/blob/147b8fecb94669e0543b9f654a61dec1cb5f79f0/research-note.tex) explicitly excludes unequal capacities; it is not a premise of this proof.

Publish as an unrefereed research manuscript with exact reproducibility evidence and a checked supporting Lean library. Use Candidate / Unreviewed for the full VibeMathed result. Retain the question-origin caveat, author responsibility, substantial AI disclosure, and lack of novelty clearance. A useful next mathematical milestone is the complete paired-factorial criterion; a full matching formalization then requires the source-count bridges listed in [SCOPE.md](../formalization/SCOPE.md).
