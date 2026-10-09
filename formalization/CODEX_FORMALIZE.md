> Historical development handoff. Phases A and B are complete. The binomial/window part of C and structural source-model parts of C-E are proved; the full probability and continuation bridges remain open. See README.md and SCOPE.md.

# Codex task: compile, complete, and audit the two-bin formalization

## Mandate

Work only on the two-bin publication package. Do not start a three-bin project, post externally, alter author/ownership/license, rewrite the mathematical target, or update historical archives. The complete paper proof is in `paper/manuscript.pdf`; the original exact package is under `evidence/`. The current Lean directory is UNCOMPILED partial source, not a proof certificate.

## Phase A — establish a real build

Use the pinned toolchain and mathlib revision. Resolve and retain `lake-manifest.json`; capture compiler version and environment. Run the supplied positive library and audit harness in a fresh working copy. Repair syntax/API issues without changing intended statements. Verify that every negative control imports the successfully built positive library and fails at its intended false claim, not because an import or toolchain is missing. Preserve outputs and source hashes.

Never use `sorry`, `admit`, new axioms, `native_decide`, `decide +native`, `Lean.trustCompiler`, `ofReduceBool`, `debug.skipKernelTC`, or custom checker bypasses. Kernel `decide` for genuinely finite controls is acceptable. Standard logical axioms `propext`, `Classical.choice`, and `Quot.sound` are permitted. Print the actual dependencies of every release theorem.

## Phase B — finish the algebraic engine first

Target: for natural `r <= q`, `QuadraticRegion r q ↔ PairedBound r q` with the definitions in `Definitions.lean` unchanged unless an independently documented statement repair is necessary.

1. Build the existing falling-factorial zero-support, monotonicity, product-splitting, converse, and step-identity lemmas.
2. Prove the cross-multiplied product-ratio bound by induction for `q=r+d`, `d>=2`, `0<=u<d`, `d*(d-1)<=2*r`. Prefer multiplication inequalities to rationals until denominators must be introduced. All positivity and zero-support cases must be explicit.
3. Expand `prod_i(mu-i+y)` around the common midpoint with nonnegative rational coefficients. Prove the symmetric-secant identity and connect it to `oddSlope_monotone`. Do not assume the required secant inequality as an unexplained hypothesis of the release theorem.
4. Establish the interior endpoint bound `r-u>=v-1`; prove the integer auxiliary inequality for every `d>=2`, including `d=2,3`. Use the product/secant bounds to finish the interior case.
5. Prove the axes and `max(u,v)>=d` cases with correct zero support. Assemble the **unconditional** paired bound under exactly the quadratic premise. The supplied `combine_product_secant` is only a conditional helper and cannot substitute for this assembly.
6. Emit a separate algebraic release theorem with printed axioms. A successful Phase B permits only the statement “paired-factorial criterion formalized,” not “matching classification formalized.”

## Phase C — exact binomial and first-saturation bridges

Use an integer-index binomial function that returns zero for negative or out-of-support lower indices. Prove Corollary 4 from the factorial inequality, including every vanishing case. Derive Pascal's window difference and show monotonicity of `R_t(s)` in singleton count. Prove the pure-singleton endpoint identity. Then identify those expressions with the `coinWords` source model's actual first-saturation distribution. Do not treat the desired survival law as an axiom or a definition of the process.

## Phase D — stochastic continuation and fixed-order sufficiency

Formalize the first-saturation stopping index and its truncation at word length. Prove no rejection before first saturation, independence of future fresh coins, the common remaining-capacity law, and pointwise monotonicity of the continuation kernel. Derive the actual finite summation-by-parts identity from the source counts. `tail_comparison_from_identity` is only the last algebraic implication: its identity hypothesis must be proved for the modeled process. Handle empty words, zero-degree jobs, never-filled paths, and zero-probability conditioning without division by zero.

## Phase E — both necessity proofs and final assembly

Prove the exact fixed-order two-flexible witness numerator (paper equation 17), then the separate uniform-arrival sum (20) and closed formula (23). Show parity gives `d^2>=N+2` in the excluded region, and prove denominator positivity. Connect the witness sign lemmas to actual source probabilities/counts; do not merely prove a negative rational expression. Establish the labeled-permutation weighting in `arrivalOrders`, and use it to average fixed-order sufficiency and prove independent random-order necessity.

Finally prove a theorem of type `FullClassificationTarget`, then Theorem 2's regime statements. Pin the final source-model statement in a separate challenge file for an independent correspondence audit. Keep the `r=a-1`, `q=b-1`, `N=a+b-2` conversion correct at `(1,1)` and other boundary cases; no natural-subtraction truncation may hide a missing premise.

## Required return

Return changed source, pinned dependencies, exact compiler/build/axiom logs, negative-control outcomes, a claim-by-claim scope matrix, and SHA-256 manifest. If only a milestone is complete, say which theorem is actually checked and list the remaining bridges. Do not upgrade the paper or VibeMathed claim beyond the completed scope. Compare the final literal model with the independent Python oracle on small examples, but do not mistake those tests for the universal bridge proof.

No public commit, release, or registry submission is requested by this formalization task.
