# Lean: checked supporting library, incomplete classification

Lean 4.19.0 compiles the supporting library. All **27 named theorems** are re-elaborated with `--trust=0` and have printed axiom dependencies contained in `{propext, Classical.choice, Quot.sound}`. The finite `decide` examples use no axioms. Three false claims fail at the intended source lines after positive import/control checks succeed.

**Neither `PairedClassificationTarget` nor `FullClassificationTarget` has a proof.** They are definitions of the desired propositions. A green build cannot upgrade either one into a checked theorem. See [SCOPE.md](SCOPE.md) and [STATUS.json](STATUS.json).

## Pinned environment

- Lean: `leanprover/lean4:v4.19.0`, compiler commit `6caaee842e94`.
- Mathlib: `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- Transitive dependency revisions: [lake-manifest.json](lake-manifest.json).
- Successful audit receipt: [../evidence/lean-audit.json](../evidence/lean-audit.json).
- Historical failed preflight: [../evidence/lean_NOT_RUN.json](../evidence/lean_NOT_RUN.json); it describes the earlier runtime, not this checked build.

## Commands

From this directory, with Lean/lake on PATH:

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get TwoBin/Definitions.lean
python3 -B build_and_audit.py --receipt /tmp/two-bin-lean-audit-new.json
```

On the macOS 26.4.1 host used for preparation, the old toolchain's compiled cache downloader failed with a Mach-O `SG_READ_ONLY` error. Running the same pinned Mathlib cache code with Lean's interpreter succeeded:

```sh
lake env lean --run .lake/packages/mathlib/Cache/Main.lean get TwoBin/Definitions.lean
```

This is a dependency-download workaround, not a proof-checker bypass. The Lean kernel, version, and theorem statements are unchanged.

## Source repairs and audit controls

The supplied `falling_add` induction did not compile: simplification left a `Nat.add` expression that the induction hypothesis did not rewrite. An explicit `change` and rewrite repair that proof without weakening its statement. The broad `import Mathlib` was replaced by the required modules to limit the download/build dependency set.

The audit now covers every named theorem, scans for forbidden proof/trust constructs, checks positive counterparts, and requires each negative control to fail at the intended claim. It no longer accepts arbitrary nonzero exits as successful false controls. The audit receipt binds the source, dependency manifest, and audit script hashes.

The finite source-model check uses the actual `coinWords`, `step`, `accepted`, tail counts, and `arrivalOrders` definitions, compared against the separate literal Python implementation. It includes empty words, zero-degree jobs, repeated degrees, swapped capacities, thresholds zero and above word length, and labeled-permutation multiplicities. This does not replace a universal correspondence proof.

The original [CODEX_FORMALIZE.md](CODEX_FORMALIZE.md) remains the development roadmap. Its remaining phases require substantive new proofs, not just compilation repairs. Do not advertise the full result as Lean-checked or Lean-verified.
