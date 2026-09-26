# U-SVC: own upper formalization, partial result

Author: AutoMathLab LRX Teamlead. Mathematical buffer scheme: Sergey Uskov, 19September text, SHA256 8547daf9560d5e022f9b5234b3ab72f661e873d14e84eadaa703b66f03336d9d; corrections A2772/B2775. These are new Lean implementations, not a republication of Sergey's manuscript/code. No third-party manuscript, graph/native source, object files or private messages are included. Owner authorized handoff for a coordinator PR; do not invent a blanket license for third-party dependencies.

## Exact checked scope

All included sources match final exit0 logs. EXPORTS_AXIOMS.json records named exports and actual axioms (only propext/Classical.choice/Quot.sound). BUILD_RECEIPT.json pins source/log hashes and local commands. Independent mathematical review of TL code remains pending. The older 53-module fresh replay is retained locally at artifacts/u-svc-portable-20260926/fresh-build/BUILD_RECEIPT.json; it covered 20 upper modules and native lower plus aggregate. UpperRecursiveInsertion was separately built successfully afterwards. No full Mathlib rebuild is claimed.

- paid_cycle_return / cycle_service: n>=2, full distinct native list p::a::ps, represented integer lifts, nonempty distinct cycle a::rest disjoint from p, explicit adjacent target congruences and sum tau=(n-1)*w. Construct entry X + signed transports + handoffs, returning p as buffer; head H+(n-1)*w; exactly tau on chosen labels and zero outside. Cost 1+k+2*sum(abs(tau)). Only a must initially be adjacent; later labels have arbitrary positions.
- ServiceTree.realize: every finite recursively nested binary transport/handoff tree satisfying the explicit arithmetic Valid predicate has an actual native paid word and exact supported effects, frame shift and length. Valid is NOT a supplied endpoint/service certificate, but its existence for an arbitrary permutation is NOT proved.
- ServiceTree.returning_service: return label, total winding and support equations plus Valid give a SubtreeService. All descendant nodes count in the compiler.
- ServiceTree.insert_valid / insert_realize: insert a returning child whose effect vanishes on the parent's inspected labels, allowing nonzero child winding; exact child+parent paid costs and frame shifts.
- 3240 literal diagnostic cycle fixtures n2..9 passed. They are self-audit, not an independent or universal proof.

## Reproduction

Use Lean4.34.0 and the included exact 9-dependency Lake lock, not lake update. The native LRX.BlockExchange dependency is intentionally external; see EXTERNAL_NATIVE_GRAPH_MANIFEST.json. Coordinator can overlay formal/*.lean into the pinned native project after attribution/rights review. Compile in topological import order, or run:

    python3 replay.py --lean /path/to/lean-4.34.0 --dependency-path /path/to/native-objects:/path/to/pinned/mathlib-and-package-objects --out /tmp/upper-fresh

The replay compiles every included module into fresh objects, rejects dependency paths containing any of these own upper modules, and emits exact commands/logs/axioms/BUILD_RECEIPT.json. For the full original LRX project use its preserved manifest/toolchain. No object files are shipped.

## Unproved gaps / next work

1. Open-root variant without entry/final X; construct exact last-buffer endpoint.
2. Select and validate a recursively inserted all-descendant plan from reachability; prove termination/contact availability, including post-movement and tau=0 contacts. Current tree compiler does not prove this geometric selector.
3. Relate macro rotation count to Delta-Lambda; remove surplus X while preserving target; prove all-n paid budget.
4. A owns lift/phase/periodic bijection/C-minimum gap; B owns ScalarCapChecked1/2; C owns paid selector. Do not duplicate them.
5. Universal native word <=n(n-1)/2 and Graph upper/equality remain open. Existing exact witness is not full upper. PR7 UpperLiftSelection is separate, independent A review pending.

Native graph/lower are external dependencies only. GraphBridge/Reachability/GraphLower: author MathSavant, delivery2626, license permission pending. No GitHub publication of this handoff is claimed; coordinator must publish a branch/PR and record its URL/commit.
