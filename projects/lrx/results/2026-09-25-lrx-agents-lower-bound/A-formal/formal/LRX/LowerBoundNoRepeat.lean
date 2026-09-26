import LRX.Cycle11StructuralBridge
import LRX.Cycle11RigidPairMoves
import Mathlib.Logic.Equiv.Basic

/-! Actual distinct-label LRX words: a shortest word cannot swap the same
unordered pair of labels twice. Both swap events are read from the same
concrete original trace. No abstract repair-gate or diameter premise remains. -/
namespace LRX.LowerBoundNoRepeat
open LRX.BlockExchange LRX.Cycle11TwoLabelRepair LRX.Cycle11StructuralBridge
variable {α : Type*} [DecidableEq α]

def HeadPair (a b : α) (s : List α) : Prop :=
  (∃ t, s=a::b::t) ∨ (∃ t, s=b::a::t)

def Shortest (w : List Op) (s : List α) : Prop :=
  ∀ v : List Op, run v s=run w s → w.length≤v.length

theorem actual_head_swap (a b : α) (s : List α)
    (hs : s.Nodup) (hp : HeadPair a b s) :
    run [.X] s=s.map (Equiv.swap a b) := by
  rcases hp with ⟨t,rfl⟩ | ⟨t,rfl⟩
  · simp only [List.nodup_cons,List.mem_cons,not_or] at hs
    exact repair_head (Equiv.swap a b) a b t (Equiv.swap_apply_left a b)
      (Equiv.swap_apply_right a b)
      (map_fixed (Equiv.swap a b) a b t
        (fun x hx hy => Equiv.swap_apply_of_ne_of_ne hx hy) hs.1.2 hs.2.1)
  · simp only [List.nodup_cons,List.mem_cons,not_or] at hs
    exact repair_head (Equiv.swap a b) b a t (Equiv.swap_apply_right a b)
      (Equiv.swap_apply_left a b)
      (map_fixed (Equiv.swap a b) a b t
        (fun x hx hy => Equiv.swap_apply_of_ne_of_ne hx hy) hs.2.1 hs.1.2)

theorem remove_repeated_actual_pair (a b : α) (s : List α)
    (u v w : List Op) (hs : s.Nodup)
    (hfirst : HeadPair a b (run u s))
    (hsecond : HeadPair a b (run (u++[.X]++v) s)) :
    run (u++[.X]++v++[.X]++w) s=run (u++v++w) s ∧
    (u++[Op.X]++v++[Op.X]++w).length=(u++v++w).length+2 := by
  have h1 := actual_head_swap a b (run u s) ((run_perm u s).nodup_iff.mpr hs) hfirst
  have h2 := actual_head_swap a b (run (u++[.X]++v) s)
    ((run_perm (u++[.X]++v) s).nodup_iff.mpr hs) hsecond
  have h2' : run [.X] (run v (run [.X] (run u s)))=
      (run v (run [.X] (run u s))).map (Equiv.swap a b) := by
    simpa only [run_append] using h2
  exact LRX.Cycle11RigidPairMoves.remove_two_pair_swaps (Equiv.swap a b)
    (fun x => Equiv.swap_apply_self a b x) u v w s h1 h2'

theorem shortest_no_repeated_pair (a b : α) (s : List α)
    (u v w : List Op) (hs : s.Nodup)
    (hfirst : HeadPair a b (run u s))
    (hsecond : HeadPair a b (run (u++[.X]++v) s)) :
    ¬Shortest (u++[.X]++v++[.X]++w) s := by
  intro hmin
  obtain ⟨hend,hlen⟩ := remove_repeated_actual_pair a b s u v w hs hfirst hsecond
  have hle := hmin (u++v++w) hend.symm
  omega

#print axioms actual_head_swap
#print axioms remove_repeated_actual_pair
#print axioms shortest_no_repeated_pair
end LRX.LowerBoundNoRepeat
