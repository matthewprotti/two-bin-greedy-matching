# Lean: algebraic criterion proved; full matching classification still open

Lean 4.19.0 checks the complete paired falling-factorial criterion under the original definitions:

```text
TwoBin.paired_classification : PairedClassificationTarget
```

For every natural `r <= q`, the quadratic condition is equivalent to the paired falling-factorial inequality for every natural `u,v`. The proof assumes no product-ratio, secant, or stochastic comparison lemma as an unexplained hypothesis.

The binomial corollary, Pascal window difference, singleton monotonicity, and pure-singleton endpoint also check. These prove `survivalFormula_dominance` for the paper's explicit binomial formulas. **The universal identification of those formulas with actual source probabilities is still open.** `FullClassificationTarget` has no proof.

All **83 named theorems** are re-elaborated with `--trust=0`; their printed axiom dependencies are contained in `{propext, Classical.choice, Quot.sound}`. Four false controls fail at their intended claims. The [scope matrix](SCOPE.md) separates complete results from remaining bridges.

## Proof organization

- `Product.lean`: complete cross-multiplied product-ratio induction, endpoint inequalities including gaps 2 and 3, and large-index/zero-support cases.
- `Symmetric.lean`: exact even/odd recurrence for the falling-factorial product, its evaluation identities, nonnegativity, and monotonicity; these prove the actual symmetric-secant inequality.
- `Paired.lean`: all-case sufficiency and the sharp equivalence with the quadratic condition.
- `Binomial.lean`: integer-index binomial coefficients and factorial conversion including every vanishing case; paper Corollary 4.
- `Window.lean`: Pascal difference, monotonicity, endpoint, and comparison of the binomial survival formulas. These are formulas, not assumed probability laws of the process.
- `SourceBridge.lean`: coin-word size and lengths, labeled-arrival size and lengths, fixed-to-random-order implication, load monotonicity, equality of actual and unconstrained no-saturation events, first-saturation index and truncation bounds.

The secant proof expresses the manuscript's coefficient argument by the recurrence `(E,O) -> (cE + h²O, E + cO)` when a factor `c+h` is added. It proves the evaluation identity and both monotonicities directly. The old generic `oddSlope_monotone` remains checked but is not needed by the release theorem. This changes the formal proof organization, not the mathematical target.

## Statement correspondence

[ChallengeStatement.lean](ChallengeStatement.lean) imports Mathlib alone and gives a separate recursive falling factorial and literal universal criterion. [AlgebraicChallenge.lean](AlgebraicChallenge.lean) proves correspondence by induction on that recursion and applies the release theorem with no extra hypotheses. This is a machine-checked statement comparison prepared in the same project; it is **not an independent human correspondence audit**.

`Definitions.lean` and `SourceModel.lean` are unchanged from the initial publication. The latter retains one persistent RK priority and independent per-job coins, including unused coins and repeated-degree arrival multiplicities.

## Reproduction

Pinned Lean: `leanprover/lean4:v4.19.0`, commit `6caaee842e94`. Mathlib: `c44e0c8ee63ca166450922a373c7409c5d26b00b`; transitive revisions are in `lake-manifest.json`.

```sh
cd formalization
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get TwoBin.lean
python3 -B build_and_audit.py --receipt /tmp/two-bin-algebraic-audit-new.json
cd ..
python3 -B scripts/check_source_model.py --receipt /tmp/two-bin-source-check-new.json
```

Receipts must use new paths outside the repository. On the preparation host (macOS 26.4.1), the old compiled cache downloader failed a Mach-O `SG_READ_ONLY` check. The same pinned cache code runs through the Lean interpreter:

```sh
lake env lean --run .lake/packages/mathlib/Cache/Main.lean get TwoBin.lean
```

This only changes dependency download execution, not the proof checker. The [audit receipt](../evidence/lean-audit.json) binds source and dependency hashes, compiler output, every theorem's actual axioms, challenge checking, and false controls. The initial 27-theorem receipt is retained as `lean-audit-phase-a.json`.

The finite cross-check covers 32,064 matching tails and 2,904 survival comparisons, including empty words, zeros, swapped capacities, repeated degrees, and out-of-range thresholds. It does not replace the missing universal probability bridges.
