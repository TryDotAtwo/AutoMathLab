import LRX.ReflectionWitnessAudit

/-! Submission entry point. Original graph, full linear permutations, unit L/R/X.
The manuscript's proved claims below have no universal upper-bound premise.
No diameter equality or universal upper bound is declared here. -/
namespace LRX.Submission

theorem diameter_lower {n : Nat} (hn : 4 ≤ n) :
    n * (n - 1) / 2 ≤ (LRX.GraphBridge.graph n).diam :=
  LRX.GraphBridge.diam_lower hn

theorem reflected_distance {n : Nat} (hn : 4 ≤ n) :
    (LRX.GraphBridge.graph n).dist
      (LRX.GraphBridge.root n) (LRX.GraphBridge.target n) = n * (n - 1) / 2 :=
  LRX.ReflectionWitnessDistance.witness_dist_eq hn

#print axioms diameter_lower
#print axioms reflected_distance
end LRX.Submission
