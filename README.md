# A sharp capacity criterion for two-bin greedy matching

**Matthew Protti · Independent Researcher · 9 October 2026 · Unrefereed research manuscript**

For two positive integer capacities `a <= b`, independent uniform singleton neighborhoods, and one independently uniform shared RANKING priority, RANDOM-VERTEX universally stochastically dominates RANKING exactly when

```text
(b-a)^2 <= a+b-2.
```

The paper establishes this classification for every fixed degree word and, separately, for every degree multiset under independent uniform random arrivals. It also classifies equality, reverse dominance, and absence of a universal ordering. It makes no claim for arbitrary fixed graphs, biased or correlated neighborhoods, adaptive arrivals, or three or more bins.

## Status and reading order

1. [Manuscript (PDF)](paper/manuscript.pdf): complete elementary paper proof. [LaTeX source](paper/manuscript.tex) and [readable proof](paper/manuscript.md) are included.
2. [Full formalization review](review/FULL_CLASSIFICATION.md), [historical algebraic milestone](review/ALGEBRAIC_MILESTONE.md), and [initial review](review/CODEX_REVIEW.md): what was checked and what remains uncertain. A positive returned review has unidentified provider provenance; no independent human expert review or peer review is claimed.
3. [Lean scope](formalization/README.md): **The full matching classification and all four regimes are proved in Lean for the original source model.** All 272 named theorems have audited axioms. Both arrival models, strict witnesses, and the paper's two closed witness formulas are checked. Independent human statement correspondence review has not been performed.
4. [Prior-work report](research/OVERLAP_REPORT.md): a bounded search found no matching classification. Novelty and priority remain uncleared. Arnosti already observed unequal-capacity reversals; the claimed contribution is the sharp classification.
5. [Claim matrix](release/CLAIM_MATRIX.json) and [scope matrix](formalization/SCOPE.md).

This is human-directed, substantially AI-developed research. The manuscript identifies the contribution of ChatGPT research sessions and Codex. AI systems are not authors. No software or manuscript license has been selected; see [RIGHTS.md](RIGHTS.md).

## Reproduce the exact computational evidence

Python 3.10+ and its standard library suffice:

```sh
python3 -B VERIFY_PACKAGE.py
```

This verifies the publication manifest, checks the pinned historical archive, and reruns its full exact-arithmetic suite in a fresh temporary copy. It excludes generated Git, Lean, and Python cache directories. The immutable October 8 archive and its historical status labels remain unchanged.

## Reproduce the full classification

Install Lean through the official Lean toolchain distribution, then use the checked-in toolchain and dependency manifest:

```sh
cd formalization
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get TwoBin.lean
python3 -B build_and_audit.py --receipt /tmp/two-bin-lean-audit.json
cd ..
python3 -B scripts/check_source_model.py --receipt /tmp/two-bin-source-model.json
```

Receipt destinations must be new paths outside the repository. See [the Lean README](formalization/README.md) for the macOS cache-downloader workaround and exact scope. The source-model comparison executes actual Lean definitions: 32,064 matching-size tail comparisons agree with the separate historical oracle, and 2,904 survival comparisons agree with both the historical formulas and the new Lean formulas. The recursive continuation kernels also agree with the original counts on 16,032 tails, and 14 bounded witness-gap checks agree with the historical formulas and oracle. These are finite execution checks; the universal source-to-probability bridges are proved separately in Lean.

The GitHub workflow repeats the manifest/replay, Lean audit, false controls, and source-model comparison. The workflow checks the full source-model classification and regimes. A successful run certifies the checked formal statements, not independent human correspondence review, novelty, or peer review. Consult the pull request for the exact revision's CI result.

## Rebuild the paper

```sh
python3 paper/build_pdf.py --out-dir /tmp/two-bin-paper-new
```

Use a new directory outside the repository. The script supports pdfLaTeX or Tectonic. The mathematical statements and display blocks are unchanged from the supplied manuscript; the verification and AI-attribution paragraphs reflect the completed formalization (10 October 2026).

