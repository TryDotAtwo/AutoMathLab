# Native graph lower bound and exact reflected witness — own supplement

- ID: 2026-09-26-lrx-agents-native-witness-supplement
- Date: 26 September 2026; underlying proof/replays: 25 September 2026.
- Authors/contributions: A/B native lower; B witness composition; coordinator Codex on behalf of Aleksei Makin, entry point and independent replay. Historical word: Astra Ultra <3. External graph: LRX_Math_Savant. See the [full contribution ledger](2026-09-26-lrx-agents-native-witness-supplement/README.md).
- Claim status: **proved**, restricted to the exact lower-bound and single-pair-distance exports in the checked complete environment.
- Verification status: **formally-checked**, including coordinator independent execution of the local modules. No human peer review or full external-library rebuild is claimed.
- Publication/reproduction status: **blocked for standalone restoration** by three external graph sources not licensed for redistribution in this intake; own files and exact dependency identities are published.
- Coordination: [Issue #8](https://github.com/TryDotAtwo/AutoMathLab/issues/8); supplements [PR #5](https://github.com/TryDotAtwo/AutoMathLab/pull/5), base commit `29264dd2a6fe412a5ee7373a02b197782745d3e4`.

For n≥4 and the original unit-cost L/R/X graph on linear permutations with distinct labels, `LRX.Submission.diameter_lower` proves n(n−1)/2 ≤ diam; `LRX.Submission.reflected_distance` proves distance from (1,…,n) to (2,1,n,…,3) equals n(n−1)/2. These statements have no universal-upper premise. **Neither diameter equality nor the universal upper is proved by this supplement.** No multiset status changes.

[Package and commands](2026-09-26-lrx-agents-native-witness-supplement/README.md), [entry source](2026-09-26-lrx-agents-native-witness-supplement/formal/Submission.lean), [external source manifest](2026-09-26-lrx-agents-native-witness-supplement/EXTERNAL_DEPENDENCIES.json), [executed replay receipt](2026-09-26-lrx-agents-native-witness-supplement/checks/REPLAY_RECEIPT.json), [SHA manifest](2026-09-26-lrx-agents-native-witness-supplement/MANIFEST.json).

Lean 4.34.0; Mathlib `5ed2965256430c3649e86755f9576b54eca72435`; nine-package lock included. All 31 module/log hashes of the prior portable replay were verified at packaging; 28 permitted sources are included, three graph sources explicitly excluded. The two entry axiom reports contain only propext, Classical.choice, Quot.sound. The 24 base modules match PR #5 byte-for-byte; the three B witness modules plus Submission are the own additions. No new compilation is implied by this integrity check.

Next: graph author provides an attributed public package/PR with distribution terms, or explicit redistribution permission. Maintainers review/merge the own supplement before submission if acceptable and bind the exact external version. Our publication contains no third-party manuscript, historical code excerpt, graph source, credentials or raw conversation. Newly prepared sources are contributed under repository terms; external authorship and the access blocker remain explicit.
