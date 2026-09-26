# Balanced phase-compatible short lifts by quadratic energy

- ID: 2026-09-26-codex-upper-lift-selection
- Author/date: local Codex coordinator, prepared on behalf of Aleksei Makin, 26 September 2026. This identifies research provenance, not an approved journal author list.
- Claim status: **proved**, restricted to `exists_majorized_short_lift` and the helper statements in the preserved source.
- Verification status: **formally-checked**, author execution; independent mathematical/replay review by A **pending**.
- Coordination: [Issue #6](https://github.com/TryDotAtwo/AutoMathLab/issues/6).
- Dependencies: Lean `leanprover/lean4:v4.34.0`; Mathlib `5ed2965256430c3649e86755f9576b54eca72435`; complete nine-package lock included.

## Exact statement

For every integer n>0 and permutation p of {0,...,n−1}, there exist an integer phase c and integer displacements d_i such that:

1. Σ_i d_i = 0.
2. i + d_i = p(i) + c + n w_i for some integers w_i (all i).
3. For every subset S of the indices, 2 Σ_{i∈S} d_i ≤ |S|(n−|S|).
4. For every i, 2|d_i| ≤ n−1; in particular |d_i| < n/2.

The exact Lean export is `LRX.UpperLiftSelection.exists_majorized_short_lift`. The source includes the complete signature. It assumes only `p : Equiv.Perm (Fin n)` and `hn : 0 < n`; neither a minimizer nor majorization is a premise of this final theorem. Labels/indices are zero-based. The phase is an integer and compatibility is an exact integer equality with windings, not a claim about a freely rotated graph vertex.

## Argument and relationship to the upper-proof program

The initial lift is d_i=p(i)−i at phase zero. Quadratic energy E(d)=Σd_i² is nonnegative; well-ordering of natural energies yields a global minimizer across all balanced compatible lifts and phases. For S of size k, the move d'_i=d_i+k−n·1_{i∈S} preserves balance and changes phase to c+k. Its exact energy change is

    E(d')−E(d)=n [k(n−k)−2Σ_{i∈S}d_i].

Minimality and n>0 give all subset bounds. Singleton and complement bounds give strict shortness. This supplies a formal route to the subset/shortness contract sought in U-LIFT. The scope resembles the phase-selection interface in the LRX upper-proof program; this package does not import any author's manuscript or claim the route is novel prior art.

**Important:** the selected minimizer minimizes quadratic energy. It is **not proved to minimize affine inversion count C**. Any downstream argument requiring C-minimality needs its own bridge or must be shown to use only the exported subset inequalities. Source semantics must be independently reviewed before integration with the general upper theorem.

## Artifacts and reproduction

[Portable package](2026-09-26-codex-upper-lift-selection/README.md), [Lean source](2026-09-26-codex-upper-lift-selection/UpperLiftSelection.lean), [original author build log](2026-09-26-codex-upper-lift-selection/build.log), [build provenance](2026-09-26-codex-upper-lift-selection/BUILD_RECEIPT.json), [SHA manifest](2026-09-26-codex-upper-lift-selection/MANIFEST.json).

From the package directory run `python3 verify.py` for a stdlib-only source-integrity check. To replay the mathematics after obtaining the pinned dependencies, run `lake exe cache get` then `python3 verify.py --lean`. No proprietary services or token credentials are needed. Original source compilation succeeded with only `propext`, `Classical.choice`, `Quot.sound` in the four named axiom reports. Packaging reused that run and did not claim another independent build.

## What is not established / handoff

No paid L/R/X word, affine-inversion minimum, buffer service, energy-to-rotation budget, finite certificate, full upper bound or diameter equality is proved here. No graph or multiset claim is silently upgraded. No independent A review is claimed yet. Next: reviewer A checks the exact semantic scope and replays the pinned source; the coordinator then binds the exported contract to only those downstream upper lemmas it actually satisfies. Record that review separately with this PR/commit and source SHA.

This publication contains only our newly prepared source, build log and packaging metadata, submitted under the repository contribution terms. No third-party proof files or private conversation are republished.
