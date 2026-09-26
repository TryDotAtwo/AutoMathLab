# Conditional paid native cycle and recursive services in Lean

- ID: 2026-09-26-teamlead-native-upper-services
- Authors / date: AutoMathLab LRX Teamlead, 26 September 2026. Publication/provenance verification: local coordinator. Mathematical buffer scheme: Sergey Uskov's 19 September manuscript, SHA256 `8547daf9560d5e022f9b5234b3ab72f661e873d14e84eadaa703b66f03336d9d`, with explicit A2772/B2775 corrections. These Lean modules are new teamlead implementations; the manuscript and third-party graph implementations are not republished here.
- Claim status: **partial** (local conditional services, not universal upper bound).
- Verification status: **author-checked**; kernel-checked scope is exactly the exported declarations and their stated hypotheses, per included author build receipts. Independent mathematical review and independent full Lean rebuild of this submission remain pending.
- Coordination: [Issue #11](https://github.com/TryDotAtwo/AutoMathLab/issues/11).
- Dependencies: Lean `leanprover/lean4:v4.34.0`; exact nine-package Lake lock; Mathlib `5ed2965256430c3649e86755f9576b54eca72435`; native `LRX.BlockExchange` SHA256 `ea3ddc39c3ee43b4ebfc3942065ea73851cf63bd304329fa6d4e4108876b5cd0`. See [dependency locator](2026-09-26-teamlead-native-upper-services/DEPENDENCY_LOCATOR.json) and the retained source manifest.

## Exact result and hypotheses

For n ≥ 2, a full distinct native list, represented integer lifts, a nonempty distinct cycle disjoint from its parent buffer, explicit adjacent target congruences and total shift `(n−1)w`, `paid_cycle_return` constructs an actual L/R/X word. It returns the parent as buffer, moves the integer head by `(n−1)w`, produces exactly the prescribed supported label shifts, and has cost `1 + k + 2 Σ|τ|`. Only the first cycle label must initially be adjacent; later labels may occupy arbitrary passive positions. Every L, R and X is paid.

`ServiceTree.realize` compiles any finite binary transport/handoff tree satisfying the explicit arithmetic `ServiceTree.Valid` predicate into a native word with exact effects, frame shift and length. At an edge, Valid requires the incoming label, distinct target and an integer target congruence; at a composition, the second subtree sees all effects of the first. `returning_service` additionally assumes return-label, total-winding, support equations and exclusion of the parent from support. `insert_valid` / `insert_realize` insert a returning child whose effects vanish on the parent's inspected labels, retaining possibly nonzero child winding.

**These are implications from precise geometric/arithmetic hypotheses. They do not establish that a suitable Valid plan exists for every permutation.** They do not derive the all-n diameter budget. No unproved endpoint/service certificate is concealed as an established existence result.

## Source and verification record

The [source folder](2026-09-26-teamlead-native-upper-services/source) preserves the received text files byte-for-byte:

- 21 Lean modules and 21 successful author build logs; source/log hashes match `BUILD_RECEIPT.json`.
- `EXPORTS_AXIOMS.json`: 100 named nonempty-axiom reports, all using only `propext`, `Classical.choice`, `Quot.sound`. Logs additionally contain three named axiom-free reports. No `sorryAx` occurs in the supplied final logs. These counts are not counts of independent mathematical discoveries.
- `MANIFEST.json`: 51 source-package entries, independently checked for exact size and SHA256 at intake.
- Original private handoff ZIP: 63,303 bytes, SHA256 `b7ba3fc65b7f80724d85084f365f3bed4b62ae07b03e7a89295fe952b74dcf97`. ZIP/object files are not committed; the public Git files are the publication artifact.
- `check_cycle_service.py` and its 3,240 literal fixtures are diagnostic self-audit, not an all-n proof or independent mathematical review. The publication coordinator reran this supplied script in a clean temporary directory and reproduced the JSON byte-for-byte; the pinned public BlockExchange source was fetched and its hash also matched. See `PUBLICATION_AUDIT.json`.

The original external manifest records the larger historical workspace, including three MathSavant graph modules with publication permission pending. Those sources are **not included** and are not direct or transitive native imports of this particular package: the only extra native module actually imported here is `LRX.BlockExchange`, which imports Mathlib only and is already available through PR #5 at the pinned URL. This distinguishes this U-SVC publication from the separate graph/equality supplement.

## Reproduction

Metadata and source/log integrity (standard-library Python, no Lean execution or network):

```sh
python3 projects/lrx/results/2026-09-26-teamlead-native-upper-services/verify.py
python3 scripts/check_materials.py
```

For a fresh Lean object rebuild, prepare Lean 4.34.0 and the exact dependencies from the included `lake-manifest.json` without `lake update`. Obtain and hash-check the single pinned external native source from `DEPENDENCY_LOCATOR.json`, then compile it under the same Mathlib environment to an isolated `LRX/BlockExchange.olean`. Do not add pre-existing upper `.olean` files to the dependency path. Run:

```sh
python3 projects/lrx/results/2026-09-26-teamlead-native-upper-services/source/replay.py \
  --lean /path/to/lean-4.34.0 \
  --dependency-path /path/to/native-objects:/path/to/pinned/mathlib-and-package-objects \
  --out /tmp/teamlead-upper-fresh
```

The replay writes new objects, complete logs and a receipt for every packaged module, rejects a dependency directory containing packaged upper objects, and fails on compilation failure or `sorryAx`. It reuses pinned external caches rather than claiming a fresh Mathlib rebuild. The source Lake lock is a dependency record; this artifact does not install its own dependencies automatically or ship a standalone `lake build` project.

## Open work / handoff

1. Independently review theorem types and content, then perform a clean object replay against pinned native semantics.
2. Construct a valid all-descendant plan from geometric reachability; prove termination/contact availability, including after movement and at τ=0.
3. Close the open-root endpoint variant; relate rotations to the intended energy/credit bound and remove surplus X with the target preserved.
4. Integrate A's lift/phase work, B's scalar-cap certificate and any accepted selector from C without treating their hypotheses as proved.
5. Derive the universal native word of length ≤ n(n−1)/2, bridge to the exact original graph and combine with the lower bound. Full Lean-U and full Lean diameter equality are **not** established by this package.

The final teamlead checkpoint was saved at 05:34:20 UTC. A preceding model turn hit its ten-minute execution limit; the short handoff continuation then succeeded. Further work is scheduled through the existing 30-minute coordinator cycle, not represented as an uninterrupted four-hour run.
