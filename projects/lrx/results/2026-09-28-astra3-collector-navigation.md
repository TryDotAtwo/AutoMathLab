# Paid two-block collector and navigation correspondence

- ID: 2026-09-28-astra3-collector-navigation
- Author/date: Astra3, 28 September2026; original implementation for Ivan's project.
- Claim status: proved for the explicitly listed local statements; full LRX remains open.
- Verification status: formally-checked, author fresh replay; no independent replay of this package claimed.
- Dependencies: official Lean4.19.0 (commit6caaee842e94), Init only, Python3.11+ for replay.

## Exact result

For arbitrary finite gap/token lists describing two nonempty groups at a chosen
token cut, an explicit L/R/X word packs the two groups in their original order.
Its intermediate cursor approach is the shorter of the actual complementary
arcs, its terminal cursor is proved, and its exact cost is proved. Both the
full-return and core variant (needed by the later cocktail sort) are included.
Separate navigation lemmas identify the metric with the source modular formula
and prove the finite-list averaged bound under an explicit site-permutation
condition. The collector's specific inter-pass endpoints are bounded and their
modular distance equals the cost of the actual chosen approach word.

The complete statements, trust boundary and open interfaces are documented in
[the package README](2026-09-28-astra3-collector-navigation/README.md).
Each letter, including rotations, has cost1. No cyclic quotient, free reflection,
Valid-plan assumption or numerical evidence replaces the word construction.

## Evidence and reproduction

Six modules were freshly compiled from this package; all25 named declarations
were audited with only propext/Quot.sound. Source and dependency hashes, exact
commands, toolchain binary hash, exit codes and raw text logs are in
[evidence/receipt.json](2026-09-28-astra3-collector-navigation/evidence/receipt.json).
Counts identify the audit surface, not a percentage of the full conjecture.

Run from the package directory with an existing Linux Lean4.19.0 installation:

```sh
python3 verify.py --lean /path/to/lean-4.19.0/bin/lean --out /path/to/new-evidence-directory
```

No installation, network, credentials, container or CI execution is initiated
automatically. Each compile is capped at1 thread,10CPU seconds,15wall seconds,
1GiB address space. The new evidence/build directory must not exist.

## What is not established

The package does not prove the final sorting stage, all-cut gap/inversion
averaging, extraction/initial approach for every arbitrary admissible input,
or global instantiation of the occupied-index permutation. In particular it
does not prove either full distinct-label LRX diameter equality or the multiset
eccentricity bound. The latter remains the originating task for n>=m>=8,
including r0,1, and is not silently restricted to the repository's r>=2 note.

Earlier local interfaces received semantic peer inspections; those are not
represented as independent compilation of this published snapshot. No foreign
archives/private conversations are included. No new license is introduced.
No global proof-map status or someone else's source has been changed.
