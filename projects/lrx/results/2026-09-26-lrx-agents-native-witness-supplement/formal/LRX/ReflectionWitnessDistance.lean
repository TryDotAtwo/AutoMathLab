import LRX.ReflectionWitness
import GraphLower

/-! Exact distance for the single historical reflected witness. The upper
direction uses its explicit paid word; the lower direction is LB-G1 dist_lower.
No universal upper bound or diameter equality is used or asserted. -/
namespace LRX.ReflectionWitnessDistance
open LRX.BlockExchange

theorem witness_dist_le {n : Nat} (hn : 4≤n) :
    (LRX.GraphBridge.graph n).dist (LRX.GraphBridge.root n) (LRX.GraphBridge.target n)
      ≤ n*(n-1)/2 := by
  obtain ⟨p,hp⟩ := LRX.GraphBridge.word_walk (by omega : 2≤n)
    (LRX.ReflectionWitness.word n) (LRX.GraphBridge.root n)
  have he : LRX.GraphBridge.runV (LRX.ReflectionWitness.word n) (LRX.GraphBridge.root n)=
      LRX.GraphBridge.target n := Subtype.ext (LRX.ReflectionWitness.word_endpoint hn)
  have hd := (LRX.GraphBridge.graph n).dist_le p
  rw [hp,LRX.ReflectionWitness.word_length hn,he] at hd
  exact hd

/-- Exact graph distance in the original, unfactored, unit-cost LRX graph. -/
theorem witness_dist_eq {n : Nat} (hn : 4≤n) :
    (LRX.GraphBridge.graph n).dist (LRX.GraphBridge.root n) (LRX.GraphBridge.target n)
      = n*(n-1)/2 := by
  exact Nat.le_antisymm (witness_dist_le hn) (LRX.GraphBridge.dist_lower hn)

#print axioms witness_dist_le
#print axioms witness_dist_eq
end LRX.ReflectionWitnessDistance
