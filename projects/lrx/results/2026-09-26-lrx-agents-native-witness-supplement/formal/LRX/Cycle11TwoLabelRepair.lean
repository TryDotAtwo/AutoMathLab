import LRX.BlockExchange

namespace LRX.Cycle11TwoLabelRepair
open LRX.BlockExchange
variable {α β : Type*}

theorem step_map (f : α → β) (op : Op) (s : List α) :
    step op (s.map f) = (step op s).map f := by
  cases op with
  | L => cases s <;> simp [step,left]
  | R => simp only [step,right,←List.map_reverse];
         have h : left (s.reverse.map f) = (left s.reverse).map f := by
           cases s.reverse <;> simp [left]
         rw [h,List.map_reverse]
  | X => cases s with
    | nil => rfl
    | cons a s => cases s <;> rfl

theorem run_map (f : α → β) (w : List Op) (s : List α) :
    run w (s.map f) = (run w s).map f := by
  induction w generalizing s with
  | nil => rfl
  | cons op w ih => simp only [run,step_map,ih]

theorem repair_head (f : α → α) (a b : α) (t : List α)
    (ha : f a=b) (hb : f b=a) (ht : t.map f=t) :
    run [.X] (a::b::t) = (a::b::t).map f := by
  simp [run,step,swap,ha,hb,ht]

theorem repair_next (f : α → α) (c a b : α) (t : List α)
    (hc : f c=c) (ha : f a=b) (hb : f b=a) (ht : t.map f=t) :
    run [.L,.X,.R] (c::a::b::t) = (c::a::b::t).map f := by
  simp [run,step,left,swap,right,ha,hb,hc,ht]

theorem repair_wrap (f : α → α) (a b : α) (t : List α)
    (ha : f a=b) (hb : f b=a) (ht : t.map f=t) :
    run [.R,.X,.L] ((b::t)++[a]) = ((b::t)++[a]).map f := by
  simp [run,step,right,swap,left,ha,hb,ht]

theorem repair_tail (f : α → α) (a b : α) (t : List α)
    (ha : f a=b) (hb : f b=a) (ht : t.map f=t) :
    run [.R,.R,.X,.L,.L] (t++[a,b]) = (t++[a,b]).map f := by
  rw [show t++[a,b] = (t++[a])++[b] by simp]
  simp [run,step,right,swap,left,ha,hb,ht,List.append_assoc]

/-- A real repair at a visited physical state transports to the final fiber.
    The repair, factor route and endpoint are for the same word, not separate minima. -/
theorem encounter_bridge (f : α → α) (u v repair : List Op)
    (s target : List α) (budget : Nat)
    (hinv : (target.map f).map f=target)
    (hend : run (u++v) s=target ∨ run (u++v) s=target.map f)
    (hrepair : run repair (run u s)=(run u s).map f)
    (hcost : repair.length≤budget) :
    ∃ w : List Op, run w s=target ∧ w.length≤(u++v).length+budget := by
  rcases hend with good | bad
  · exact ⟨u++v,good,by omega⟩
  · refine ⟨u++repair++v,?_,?_⟩
    · rw [run_append,run_append,hrepair,run_map]
      rw [←run_append,bad,hinv]
    · simp only [List.length_append]
      omega

#print axioms run_map
#print axioms repair_head
#print axioms repair_next
#print axioms repair_wrap
#print axioms repair_tail
#print axioms encounter_bridge
end LRX.Cycle11TwoLabelRepair
