# Lean: full matching classification and all four regimes

Lean 4.19.0 checks the complete capacity criterion for the original literal process, for both fixed degree words and independent uniform labeled arrival orders:

```text
TwoBin.full_classification : FullClassificationTarget
TwoBin.four_regimes : FourRegimeTarget
```

For every positive integer `a <= b`, universal RANDOM-VERTEX stochastic dominance holds exactly when `(b-a)^2 <= a+b-2`. The second theorem covers universal equality, universal RANKING dominance, universal RANDOM-VERTEX dominance, and absence of either universal ordering, with strict examples in both arrival models. The actual fixed and uniform-arrival witness probabilities equal paper equations (17) and (23).

All **272 named theorems** are re-elaborated with `--trust=0`; printed dependencies are contained in `{propext, Classical.choice, Quot.sound}`. Seven false controls fail at their intended claims. There are no admitted results, added axioms, native decision procedures, or checker bypasses. This is **end-to-end Lean-checked, with independent human statement correspondence review still outstanding**.

## Proof organization

- `Product`, `Symmetric`, `Paired`, `Binomial`, `Window`: product-ratio induction, exact even/odd secant recurrence, paired-factorial equivalence, zero-support binomial conversion, and survival-formula comparison.
- `SourceBridge`, `FiniteProbability`, `ChoiceDistribution`, `SurvivalDistribution`: the original fair-coin process, finite expectations, unconstrained binomial law, and identification of actual no-saturation probabilities with the formulas.
- `Continuation`, `TailExpansion`: common continuation after saturation, nonnegative continuation gains, and the exact finite prefix expansion of actual matching tails. `source_tail_expansion` proves the identity from the source process; it does not assume the desired identity. This yields fixed-order sufficiency.
- `WordStatistics`, `Insertion`: labeled-permutation correspondence, distinct label permutations, repeated-degree multiplicities, and exact two-flexible insertion counts.
- `AllMatched`, `GapFormula`, `FixedWitness`, `WitnessExpansion`, `UniformAlgebra`, `UniformWitness`, `WitnessIdentities`: both necessity proofs, parity and denominator boundaries, weighted finite sums, the full classification, and the two closed witness identities.
- `UnitReverse`, `StrictRV`, `StrictRandom`, `Regimes`, `FourRegimes`: reverse dominance, equality boundaries, strict examples, and all four regimes.

The continuation proof uses exact finite expectations and a prefix-gain decomposition. Zero-degree jobs contribute zero gain; prefix positive-job counts and the raw arrival index are kept distinct. This avoids conditioning on events of probability zero. Empty words, never-filled paths, dummy coins, boundary capacities, and zero-support terms are included. The formal proof organization differs from the exposition without changing the target.

## Statement correspondence and frozen definitions

[FullChallengeStatement.lean](FullChallengeStatement.lean) expands the capacity, dominance, reverse-dominance, and equality claims using only the original source definitions. [FullChallenge.lean](FullChallenge.lean) proves those literal contracts. The earlier Mathlib-only algebraic challenge remains checked. These are project-authored machine-checked correspondence artifacts, **not an independent expert audit**.

`Definitions.lean` and `SourceModel.lean` are byte-for-byte unchanged from publication commit `fa1f8d8483f11526ea32f90d14fc243f25245560`, enforced by [MODEL_LOCK.json](MODEL_LOCK.json). Historical comments calling a statement an unproved target are retained in those frozen files; its proof is now in `UniformWitness.lean`. The model retains one persistent RK priority, independent per-job coins (including unused coins), and the multiplicity of labeled arrivals with repeated degrees.

## Reproduction

Pinned Lean: `leanprover/lean4:v4.19.0`, commit `6caaee842e94`. Mathlib: `c44e0c8ee63ca166450922a373c7409c5d26b00b`; transitive revisions are in `lake-manifest.json`.

```sh
cd formalization
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get TwoBin.lean
python3 -B build_and_audit.py --receipt /tmp/two-bin-full-audit-new.json
cd ..
python3 -B scripts/check_source_model.py --receipt /tmp/two-bin-source-check-new.json
```

Receipts must use new paths outside the repository. On the preparation host (macOS 26.4.1), the compiled cache downloader failed a Mach-O `SG_READ_ONLY` check. The same pinned cache code runs through Lean's interpreter:

```sh
lake env lean --run .lake/packages/mathlib/Cache/Main.lean get TwoBin.lean
```

This only changes dependency download execution. The [audit receipt](../evidence/lean-audit.json) binds source and dependency hashes, compiler output, every theorem's axioms, literal challenges, model lock, and seven false controls. Historical 27- and 83-theorem receipts remain as `lean-audit-phase-a.json` and `lean-audit-algebraic.json`.

The separate executable crosscheck covers 32,064 matching tails, 16,032 additional recursive-kernel agreements, 2,904 survival comparisons, and 14 witness gaps against the historical Python implementations. These bounded tests supplement the universal proofs.
