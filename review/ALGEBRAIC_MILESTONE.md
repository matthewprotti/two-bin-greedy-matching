> Historical milestone, superseded by [the full classification](FULL_CLASSIFICATION.md). The open obligations described below are now proved. Its original audit is retained as `evidence/lean-audit-algebraic.json`.

# Algebraic formalization milestone — 9 October 2026

The complete paired falling-factorial classification is now proved in Lean under the original `PairedClassificationTarget`. This is the paper's algebraic engine, including both directions, all natural indices, and zero-support boundaries. The full matching classification remains open in Lean.

The checked chain is: product-ratio induction; symmetric-secant comparison; interior endpoint and large-index cases; paired-factorial equivalence; factorial/binomial conversion; Pascal window difference; singleton monotonicity; pure-singleton endpoint; comparison of the explicit survival formulas.

The secant argument uses an exact even/odd product recurrence rather than an explicit coefficient array. Its evaluation identities and monotonicity are proved. The release theorem has only the original ordering and quadratic hypotheses; no desired bound is imported as an assumption.

A separate Mathlib-only statement file repeats the literal criterion and falling-factorial recursion. The challenge proof identifies the recursions by induction and checks the release theorem against that statement. This provides a reviewable correspondence artifact, not independent author or expert verification.

The source-model work proves sample-space and arrival-order sizes, the fixed-to-random-order implication, monotone loads, equivalence of actual and unconstrained no-saturation events, and a bounded first-saturation stopping index. The next substantive bridge is identifying those actual source counts with the binomial formulas for every word. Common continuation, the actual summation-by-parts identity, witness probability formulas, and final classification assembly also remain open.

Validation comprises the full positive build, trust-zero re-elaboration, all 83 named theorem axiom reports, the literal statement comparison, and four deliberately false controls rejected at their claims. Dependencies are restricted to the standard axioms `propext`, `Classical.choice`, and `Quot.sound`. Finite source-model cross-checks cover 32,064 matching tails and 2,904 survival comparisons against the historical implementations.

The historical classification archive, core target definitions, literal process definitions, Lean version, and dependency revisions are unchanged. See [SCOPE.md](../formalization/SCOPE.md) for the precise claim boundary and [lean-audit-algebraic.json](../evidence/lean-audit-algebraic.json) for the compiler evidence.
