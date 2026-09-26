# Native lower and exact reflected witness: our additions

**Standalone replay is blocked until three external graph sources can be supplied with redistribution permission.** This package intentionally omits `GraphBridge.lean`, `Reachability.lean`, `GraphLower.lean`, authored by LRX_Math_Savant. Their exact identity, archive size, hash and source location are in `EXTERNAL_DEPENDENCIES.json`. A private group URL is not a public dependency download. We request a separate attributed graph-source PR or explicit redistribution terms in Issue #8.

## Proven claims, with the explicitly named external graph dependency

For every n≥4, the original graph on all linear permutations of n distinct labels, with L/R cyclic shifts and X exchanging the first two positions, each costing one, satisfies:

- `LRX.Submission.diameter_lower`: n(n−1)/2 ≤ graph.diam.
- `LRX.Submission.reflected_distance`: graph.dist(root,target) = n(n−1)/2, where root=(1,…,n), target=(2,1,n,…,3).

These were checked without a universal upper-bound premise. They do not prove graph.diam = n(n−1)/2 or the universal upper bound. The graph is not a quotient by rotations. n=3 is excluded. Native word semantics use zero-based Fin labels; the displayed witnesses above use labels 1…n.

## Provenance and what changed beyond PR #5

The 24 A/B native lower modules are unchanged from PR #5 commit `29264dd2a6fe412a5ee7373a02b197782745d3e4`; each exact matching path is recorded in the replay receipt. They formalize the structural/native-trace chain and exceptional cases. A supplied the interval zig formalization and native→trace/composition; B supplied folded transport and exceptional cases. Their prior analytic and formal packages are not re-authored here.

The added B files are `ReflectionWitness.lean`, `ReflectionWitnessDistance.lean`, `ReflectionWitnessAudit.lean`. They formalize the balanced two-block composition of the existing historical word, its paid transfer, endpoint/length and graph-distance equality. The historical construction belongs to Astra Ultra <3, 16 September 2026, message 1268, report §6; no new discovery of that word or priority over prior literature is claimed. The graph layer and its connectivity/dist/diam exports are LRX_Math_Savant's contribution, explicitly withheld pending distribution terms. Coordinator Codex on behalf of Aleksei Makin added `Submission.lean`, independent replay and this packaging. This is a provenance ledger, not a final human author list.

PR #5 has native-word lower, not these later graph/exact-distance entry statements. Its 24 source files are repeated here only to pin all permitted local dependencies for eventual restoration. No files or claims in PR #5 were changed. Full graph restoration remains blocked by the named external sources, not by a new mathematical gap in the already checked lower/witness chain.

## Actual verification versus packaging checks

On 25 September 2026 the coordinator freshly compiled all 30 original B-package local modules independently of B's author compilation, then checked the added Submission entry. A further portable replay compiled all 31 modules into fresh local objects; all exit codes were zero. It used Lean 4.34.0, the exact included lock, and reused pinned external Mathlib/package caches. All nine installed dependency Git HEADs matched the lock. This is a distinct execution, not human peer review or a full Mathlib rebuild.

`checks/REPLAY_RECEIPT.json` retains every source/log hash and outcome of that portable replay. It normalizes machine-specific command paths to placeholders and records the original receipt hash. All 31 logs are preserved byte-for-byte; our 28 included source files match those executed hashes. The three excluded source hashes match the original graph archive. Both Submission axiom reports contain only `propext`, `Classical.choice`, `Quot.sound`.

Packaging on 26 September checked identities and repository structure; no new heavy Lean build was performed. Hash checking alone does not establish a theorem. There are 28 included sources and three absent external graph sources, not a standalone 31-source distribution.

## Reproduce after the source-access blocker is resolved

First `python3 verify.py` checks our published files and historical receipt identities. It reports the external-source limitation explicitly. It does not invoke Lean.

Once the graph author has provided the three exact files with appropriate access/permission, place them in `formal/` and run `python3 verify.py --external` to check their exact identities. Do not substitute a different graph package silently. Then, with Elan installed:

```sh
cd formal
lake exe cache get
LEAN_EXE="$(elan which lean)"
cd ..
python3 replay.py --lean "$LEAN_EXE" --packages formal/.lake/packages --output replay-new
```

This script compiles all modules reachable from Submission into a fresh output directory and checks pinned dependency HEADs. It rejects existing output; do not run `lake update`. It requires network only for the initial pinned toolchain/dependency/cache retrieval. The current publication does not supply or download the withheld graph sources automatically. Inspect final `replay-new/Submission.log` for the two exact axiom reports and `REPLAY.json` for 31 successful rows.

## Next action

Graph author: please publish the three attributed source modules with distribution terms or explicitly permit their redistribution. Maintainers: please review and, if acceptable, merge this own-additions PR before submission; then bind the graph-source PR/version to this manifest. Until then, describe this as a verified result in a specified environment with a publication/reproducibility blocker, not a fully standalone public proof package.
