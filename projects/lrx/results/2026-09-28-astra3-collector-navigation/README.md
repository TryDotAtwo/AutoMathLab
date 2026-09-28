# Paid LRX collector and navigation lemmas

Authored by Astra3 for Ivan's LRX project, 28 September2026. These are original
Lean source files from this work; no third-party proof archive, private
conversation, credentials or binary dependency is redistributed. No new
license is introduced by this submission.

## Precise scope

The state is the visible list. L rotates left by one, R rotates right by one,
and X exchanges its first two entries. Every letter costs1; rotations are
NOT quotiented out. The exact declarations are in declarations.txt.

- BlockTransport: a nonempty block crosses one or arbitrarily many equal
  symbols leftward; exact word cost3k-1 per crossing. Paid zero-gap repair.
- BlockTransportRight: corresponding rightward word, with cursor on the
  last token and the same exact cost. No free reflection is used.
- GrowingCollector: both explicit recursive growing passes and central-gap
  merge, with complete visible-list effects and exact cost recurrence.
- TwoBlockCollector: one word composes both passes, the actual shortest
  inter-pass cursor rotation, and merge. Full-return and core variants have
  distinct, explicitly proved terminal cursor positions and costs.
- Navigation: pointwise and finite-list navigation bounds; the coordinate
  lists must be permutation-equivalent. Includes equivalence with the source
  modular metric for bounded representatives.
- CollectorNavigation: the forward/backward arcs cover the actual input;
  their minimum is exactly the source modular distance between the two
  specific inter-pass endpoint coordinates relative to the selected cut.

The collector accepts arbitrary natural gap lengths and token lists, with
one distinguished initial/final token ensuring each of its two groups is
nonempty. No Valid-plan or reachability hypothesis replaces its construction.
It packs labels in their original circular order; it does NOT sort them.
The core variant ends at offset a in that packed block, as required by the
subsequent cocktail route, rather than assuming a free return to its start.

## Not established

This package does not extract the gap representation from every admissible
input, pay the original cursor's approach for all cuts, instantiate global
cyclic-index averaging, prove gap/inversion averaging, or formalize the final
sorting stage. Neither the full multiset eccentricity bound nor the distinct-
label LRX diameter conjecture is proved here. No finite-case counts are used
as a substitute for universal statements.

The mathematical construction grew from this four-peer round's block-transport
and two-block arguments (Astra1/Astra4); the Lean implementations/proofs in this
package are Astra3's. Peer inspection of earlier local interfaces is not an
independent replay of this published snapshot.

## Reproduce

Use an already installed official Lean4.19.0 and Python3.11+ on Linux. No
Mathlib, installation, network, Docker or server changes are required:

```sh
python3 verify.py --lean /path/to/lean-4.19.0/bin/lean --out /path/to/new-evidence-directory
```

The destination must not exist. Each Lean process is limited to1 thread,
10CPU seconds,15wall seconds and1GiB address space. The source disables
asynchronous elaboration to remain within that existing small-runtime profile.
The script uses a minimal child environment, never inherits/reads credentials,
and builds dependencies only in the new evidence directory.

Expected: success=true; every listed declaration audited; axioms are confined
to propext and Quot.sound. No sorry/admit/new axioms/native_decide. The receipt
binds exact source, toolchain binary, generated dependency hashes, commands,
logs and exit codes. This records reproducibility, not an external attestation.
Saved text logs and receipt from the author's fresh package replay are under
evidence/. They do not establish any of the unproved global claims above.
