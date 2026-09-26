import LRX.LowerBoundExceptionalReduction

/-! Identification of the finite-label endpoint with the stated LRX target. -/
namespace LRX.LowerBoundExceptionalEndpoint
open LRX.LowerBoundExceptionalNative

theorem root_values (n : Nat) : (root n).map Fin.val=List.range n := by
  unfold root
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.finRange_succ_last, List.map_append]
    simpa [List.map_map, Function.comp_def, List.range_succ] using
      congrArg (fun l => l++[n]) ih

/-- Zero-based values [1,0,n-1,n-2,...,2], i.e. (2,1,n,...,3)
after adding one to each label. -/
theorem target_values {n : Nat} (hn : 2≤n) :
    (target n).map Fin.val=[1,0]++(List.range' 2 (n-2)).reverse := by
  unfold target
  rw [List.map_rotate, List.map_reverse, root_values]
  have hr : List.range n=[0,1]++List.range' 2 (n-2) := by
    calc
      List.range n=List.range (2+(n-2)) := congrArg List.range (by omega)
      _ = [0,1]++List.range' 2 (n-2) := by
        rw [List.range_add, ← List.range'_eq_map_range]
        rfl
  rw [hr, List.reverse_append]
  simpa using List.rotate_append_length_eq ((List.range' 2 (n-2)).reverse) [1,0]

#print axioms root_values
#print axioms target_values
end LRX.LowerBoundExceptionalEndpoint
