# Independent fresh replay of teamlead upper modules
- ID: 2026-09-26-codex-teamlead-upper-fresh-replay
- Reviewer / date: Codex coordinator for Aleksei Makin / 2026-09-26
- Claim status: partial
- Review status: independently-reproduced; formally-checked only for named conditional exports
- Reviewed record: 2026-09-26-teamlead-native-upper-services, PR13 commit `524deafb11509f119b9e0638890782ac689e3754`.
- Verdict: PASS for fresh compilation of all 21 packaged modules plus fresh BlockExchange; not a proof of the complete upper bound.

## Method and exact result
The coordinator copied the pinned PR sources to a separate directory on the existing authorized Railway node. The author's replay.py compiled every local module in topological order into new objects, rejecting dependency paths containing these modules' old objects. LRX.BlockExchange was also compiled fresh from public source SHA256 ea3ddc39c3ee43b4ebfc3942065ea73851cf63bd304329fa6d4e4108876b5cd0.

Lean 4.34.0 and all nine dependency source commits matched the package lock. Mathlib/package caches were reused; a fresh machine or complete Mathlib rebuild is not claimed. The first SSH transport failed before creating a remote build; the successful attempt sent the reviewed script through stdin.

All 21 modules and BlockExchange returned exit0. Completed 2026-09-26T07:59:12Z. The 100 named axiom reports use only propext, Classical.choice and Quot.sound; three additional reports are axiom-free. No sorryAx occurred. Source hashes match the pinned package. Compiler warnings are retained.

## Reproduction
Follow the result package's dependency locator. Compile BlockExchange into a new dependency directory using only the pinned Mathlib/package paths, then run:

```sh
python3 source/replay.py --lean /path/to/lean-4.34.0 --dependency-path /fresh/blockexchange:/pinned/package/caches --out /fresh/upper-build
```

Exact executed commands and original outputs are in the adjacent fresh-build/BUILD_RECEIPT.json, per-module logs, DEPENDENCY_BUILD.log, DEPENDENCIES_VERIFIED.json and REPLAY.log. MANIFEST.json pins these public copies. This is independent execution of the author's replay procedure, not a separately implemented proof kernel.

## Scope and unproved parts
Source inspection confirms ServiceTree.realize still assumes its explicit arithmetic Valid predicate. Returning/insertion services additionally require the stated support, winding and disjointness hypotheses. The replay does not prove universal valid-plan selection, termination, the global paid budget, the native upper bound, or diameter equality.

Only the original 21 PR13 modules are covered. Later UpperOpenRoot, UpperRecursiveModulo and forest additions are not covered. Full analytical and human review remain separate. Recommend archiving these named conditional exports as independently reproduced while preserving the global open obligations.
