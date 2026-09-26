# B: scalar enumeration and external-family baseline

- ID: 2026-09-26-lrxavm2-scalar-enumeration-baseline
- Authors / date: lrxavm2_bot (Agent B), 26 September 2026; publication packaging by Aleksei Makin's Codex coordinator.
- Claim status / Статус утверждения: proved, **only for the 29 listed local/conditional Lean statements**; full upper-bound project remains partial.
- Verification status / Статус проверки: formally-checked for the listed statements. Teamlead reported independent reproduction in board message 2845; this import separately checks source/log integrity, not a fresh mathematical review.
- Related work: [issue 9](https://github.com/TryDotAtwo/AutoMathLab/issues/9), [intake issue 1](https://github.com/TryDotAtwo/AutoMathLab/issues/1).
- Dependencies: Sergey Uskov, readable source of 19 September 2026, §§12/14, SHA-256 `8547daf9560d5e022f9b5234b3ab72f661e873d14e84eadaa703b66f03336d9d`; Lean 4.34.0; Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435` and exact transitive lock included.

## Exact scope

`LRX.UpperScalarRows.Admissible k r` is a predicate on nine integer fields `t,p,f,eps,a,U,m,v,x`, with `k=1 ∨ k=2`, rectangular ranges and explicit scalar filters. The source defines the exact inequalities; this record does not replace their assumptions with geometric conclusions about arbitrary permutations.

| Module | Proven local result |
|---|---|
| UpperScalarRows | Membership equivalence for the direct finite row enumeration; elementary range consequences. |
| UpperScalarSqrt | Floor/ceiling square-root comparisons and union of the two square-envelope branches. |
| UpperScalarPruning | Equivalence and coverage of the accelerated x branches under the stated bounds. |
| UpperScalarRanges | Coverage of m/v ranges for an admissible row; integer truncation/division agreement under explicit hypotheses. |
| UpperScalarEnumeration | `mem_prunedRows` and `prunedRows_eq_rows`: accelerated and direct enumeration specify exactly the same admissible rows. |
| UpperExternalFamilies | Exact catalogue of permutations of lengths 2–5 without an empty cut; soundness/completeness of ordered families under the stated count/mass hypotheses. |
| UpperExternalCatalogueCheck | Catalogue cardinality 88, computed by `decide +kernel`. |
| UpperScalarExternalBridge | Conditional `external_family_of_scalar_cap`, requiring an independently supplied `ScalarCapChecked k` and validity/count/mass hypotheses. |

Every audited export and source file is listed in [THEOREMS.json](2026-09-26-lrxavm2-scalar-enumeration-baseline/THEOREMS.json). Exact statements are in the eight [Lean source modules](2026-09-26-lrxavm2-scalar-enumeration-baseline/formal/LRX). The umbrella imports all eight through their dependency graph. Only `propext`, `Classical.choice`, `Quot.sound` occur in the final axiom reports.

## Evidence and provenance

B's completed build ran 26 September 00:58:48–00:59:08 UTC; umbrella checked at 01:00:22 UTC. The original [BUILD_RECEIPT.json](2026-09-26-lrxavm2-scalar-enumeration-baseline/BUILD_RECEIPT.json), final logs, source bytes, toolchain and lock are preserved unchanged. Absolute container paths in this historical receipt document that build; they are **not required** by the portable verifier.

Source archive in group message 2844: 128,621 bytes; SHA-256 `163f06f634f6db7137a45113365a01f2644d36bff889318aa8041fec1202af34`. The coordinator fetched that immutable archive, verified the hash and extracted only B's completed source/environment/final-log baseline. [SOURCE_MANIFEST.json](2026-09-26-lrxavm2-scalar-enumeration-baseline/SOURCE_MANIFEST.json) pins the extracted files. The original ZIP also contains research inputs and private board excerpts; it is deliberately not republished.

In message 2845, `lrxavm_teamlead_bot` reported independent reconstruction of eight modules and 29 axiom reports after checking archive/file integrity, explicitly accepting only these local results. This is an attributed review report; no invented fresh review logs or reviewer identity are added here. See [the review provenance note](../reviews/2026-09-26-coordinator-b-baseline-import.md).

The owner authorized publishing the work of their agent B. These Lean modules are B's formalization; the mathematical source is attributed to Sergey Uskov. His source text, original C++, corrections by other authors and chat transcripts are not redistributed here. No MathSavant/native-graph source is imported or needed: module imports refer only to Mathlib and this package's own `LRX.*` modules.

## Reproduction

See [README and commands](2026-09-26-lrxavm2-scalar-enumeration-baseline/README.md). The standard-library verifier checks exact hashes and 29 matching historical axiom reports without downloads. Optional `--build` recompiles in an isolated temporary directory, validates all pinned dependency revisions and writes new logs outside the preserved baseline. It does not modify the running agent's research files or historical receipts.

## What is NOT proved

- `ScalarCapChecked 1` and `ScalarCapChecked 2`: the cap `r.v - 2*(r.t-1) ≤ 5` over the scalar rows is **not** supplied by this baseline. The finite scalar row set has not been fully evaluated by the kernel here.
- All external exclusions, SCC/credit/sign statistics and refinements.
- Geometric necessity of the scalar assumptions for every original LRX permutation.
- Full refinement of C++ machine execution, including overflow and binary root-search implementation.
- The complete universal Lean upper bound or diameter equality.

The currently running ScalarCap certificate development is a later package. Generated trees or interrupted trial builds are not included or counted as verified results in this publication.

## Handoff

Continue B's existing U-CERT task: close `ScalarCapChecked 1`, then the conditional geometry/exclusion interface. Preserve this baseline unchanged. Add new results and independent reviews separately with exact source hashes and successful full kernel logs. There is no new heavy computation or new agent launched by this PR.
