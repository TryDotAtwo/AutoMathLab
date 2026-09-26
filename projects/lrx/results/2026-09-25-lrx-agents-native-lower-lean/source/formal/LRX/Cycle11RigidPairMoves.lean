import LRX.Cycle11PairEncounter

namespace LRX.Cycle11RigidPairMoves
open LRX.BlockExchange
open LRX.Cycle11TwoLabelRepair
variable {α : Type*}

/-- Move a contiguous oriented pair across one neighbor. The intermediate
separation is exactly the paid three-letter primitive XLX. -/
theorem next_to_wrap (x a b : α) (t : List α) :
    run [.X,.L,.X] (x::a::b::t)=(b::x::t)++[a] := by
  simp [run,step,swap,left]

theorem wrap_to_next (x a b : α) (t : List α) :
    run [.X,.R,.X] ((b::x::t)++[a])=x::a::b::t := by
  simp [run,step,swap,right,left]

/-- Two actual swaps of the same selected labels can be removed together.
This preserves the endpoint and saves exactly two paid letters. The two gate
hypotheses concern the original same path, not independently chosen minima. -/
theorem remove_two_pair_swaps (f : α → α) (hinv : Function.Involutive f)
    (u v w : List Op) (s : List α)
    (hfirst : run [.X] (run u s)=(run u s).map f)
    (hsecond : run [.X] (run v (run [.X] (run u s)))=
      (run v (run [.X] (run u s))).map f) :
    run (u++[.X]++v++[.X]++w) s=run (u++v++w) s ∧
    (u++[Op.X]++v++[Op.X]++w).length=(u++v++w).length+2 := by
  have hm (p : List α) : (p.map f).map f=p := by
    simp only [List.map_map]
    have he : f ∘ f=id := by funext a; exact hinv a
    rw [he,List.map_id]
  have h : run [.X] (run v (run [.X] (run u s)))=run v (run u s) := by
    rw [hsecond,hfirst,run_map,hm]
  constructor
  · simp only [run_append]
    rw [h]
  · simp only [List.length_append,List.length_cons,List.length_nil]
    omega

#print axioms next_to_wrap
#print axioms wrap_to_next
#print axioms remove_two_pair_swaps
end LRX.Cycle11RigidPairMoves
