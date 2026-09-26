# Publication review of B scalar baseline

- ID: 2026-09-26-coordinator-b-baseline-import
- Reviewer / date: Aleksei Makin's Codex coordinator, 26 September 2026.
- Claim status: proved for the artifact-integrity observations below, not a new proof of U.
- Verification status: author-checked publication packaging. Formal status of the imported mathematical statements is recorded separately in the result.
- Target: [B baseline](../results/2026-09-26-lrxavm2-scalar-enumeration-baseline.md); source archive SHA-256 `163f06f634f6db7137a45113365a01f2644d36bff889318aa8041fec1202af34`.

## Checks actually performed by the publication coordinator

1. Fetched the immutable completed archive from B's existing authorized service; verified size 128621 and exact archive SHA-256.
2. Preserved source/environment/final-log bytes; checked all eight source/log hash pairs against `BUILD_RECEIPT.json`, which reports exit code 0 for each module.
3. Matched all 29 `#print axioms` declarations to final reports and restricted dependencies to `propext`, `Classical.choice`, `Quot.sound`.
4. Checked imports: only Mathlib and package-local modules; no dependency on unpublished MathSavant or native graph files.
5. Checked the portable integrity verifier and its rejection of a deliberately corrupted temporary copy; ran `python scripts/check_materials.py` on the staged publication.

These are provenance/integrity and packaging checks, not a fresh independent Lean rebuild in this coordinator session.

## Independent mathematical verification reported elsewhere

Telegram board message 2845 by `lrxavm_teamlead_bot` reports independent rebuild of the same 8 modules and audit of the same 29 exports, after checking the archive and file hashes. It explicitly leaves `ScalarCapChecked` and geometric necessity as unproved assumptions. This record preserves the attribution and scope. The separate full independent-rebuild receipt is not supplied in this publication, so readers should use the pinned sources and portable command for their own replay.

## Remaining review

Run a fresh kernel build in a separately provisioned pinned environment. Review that the chosen scalar predicate really follows from the U19 geometry; do not treat the finite-enumeration equivalence as that missing implication. Verify later cap packages against new receipts rather than upgrading this baseline's status silently.
