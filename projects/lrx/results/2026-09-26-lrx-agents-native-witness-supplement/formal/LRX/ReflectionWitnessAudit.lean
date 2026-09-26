import LRX.ReflectionWitnessDistance

-- Explicit contract checks: actual Fin-list vertices, not a rotation quotient.
example {n : Nat} (hn : 4≤n) :
    LRX.BlockExchange.run (LRX.ReflectionWitness.word n) (List.finRange n) =
      (List.finRange n).reverse.rotate (n-2) :=
  LRX.ReflectionWitness.word_endpoint hn

example {n : Nat} (hn : 4≤n) :
    (LRX.ReflectionWitness.word n).length=n*(n-1)/2 :=
  LRX.ReflectionWitness.word_length hn

example {n : Nat} (hn : 4≤n) :
    (LRX.GraphBridge.graph n).dist
      ⟨List.finRange n, List.Perm.refl _⟩
      ⟨(List.finRange n).reverse.rotate (n-2),
        (List.rotate_perm _ _).trans (List.reverse_perm _)⟩ = n*(n-1)/2 :=
  LRX.ReflectionWitnessDistance.witness_dist_eq hn

#check LRX.ReflectionWitness.transfer_length
#print axioms LRX.ReflectionWitness.transfer_length
#check LRX.ReflectionWitness.inverse_length
#print axioms LRX.ReflectionWitness.inverse_length
#check LRX.ReflectionWitness.full_spin
#print axioms LRX.ReflectionWitness.full_spin
#check LRX.ReflectionWitness.spin_add_period
#print axioms LRX.ReflectionWitness.spin_add_period
#check LRX.ReflectionWitness.transfer_cursor
#print axioms LRX.ReflectionWitness.transfer_cursor
#check LRX.ReflectionWitness.transfer_run
#print axioms LRX.ReflectionWitness.transfer_run
#check LRX.ReflectionWitness.inverse_zig_run
#print axioms LRX.ReflectionWitness.inverse_zig_run
#check LRX.ReflectionWitness.two_block_endpoint
#print axioms LRX.ReflectionWitness.two_block_endpoint
#check LRX.ReflectionWitness.word_length
#print axioms LRX.ReflectionWitness.word_length
#check LRX.ReflectionWitness.word_endpoint
#print axioms LRX.ReflectionWitness.word_endpoint
#check LRX.ReflectionWitnessDistance.witness_dist_le
#print axioms LRX.ReflectionWitnessDistance.witness_dist_le
#check LRX.ReflectionWitnessDistance.witness_dist_eq
#print axioms LRX.ReflectionWitnessDistance.witness_dist_eq
#check LRX.Cycle11BlockReversal.zig_run
#print axioms LRX.Cycle11BlockReversal.zig_run
#check LRX.Cycle11BlockReversal.zig_length
#print axioms LRX.Cycle11BlockReversal.zig_length
#check LRX.GraphBridge.word_walk
#print axioms LRX.GraphBridge.word_walk
#check LRX.GraphBridge.dist_lower
#print axioms LRX.GraphBridge.dist_lower
