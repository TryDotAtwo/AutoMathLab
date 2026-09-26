import LRX.Cycle11WordSymmetry
import LRX.LowerBoundProjectionBarrier

/-! Twisted cyclic rebase of actual reflection words. Same input, same target,
same total length and rotation count. No free cursor rotation is appended. -/
namespace LRX.LowerBoundTwistedRebase
open LRX.BlockExchange LRX.Cycle11StructuralBridge LRX.Cycle11WordSymmetry
open LRX.Cycle11TwoLabelRepair LRX.LowerBoundProjectionBarrier
variable {α : Type*} [DecidableEq α]

def rebase (u v : List Op) : List Op := v++mirror u

theorem reflect_map (f : α → α) (s : List α) :
    reflect (s.map f)=(reflect s).map f := by
  cases s with
  | nil => rfl
  | cons a t => cases t <;> simp [reflect,List.map_reverse]

theorem rename_exists (t s : List α) (ht : t.Nodup) (hlen : t.length=s.length) :
    ∃ f : α → α, t.map f=s := by
  induction t generalizing s with
  | nil =>
    have hs : s=[] := List.eq_nil_of_length_eq_zero hlen.symm
    subst s
    exact ⟨id,rfl⟩
  | cons a t ih =>
    cases s with
    | nil => simp at hlen
    | cons b s =>
      have hn := (List.nodup_cons.mp ht).1
      have ht' := (List.nodup_cons.mp ht).2
      obtain ⟨f,hf⟩ := ih s ht' (by simpa using hlen)
      refine ⟨fun x => if x=a then b else f x,?_⟩
      simp only [List.map_cons,ite_true]
      congr 1
      have he : t.map (fun x => if x=a then b else f x)=t.map f := by
        apply List.map_congr_left
        intro x hx
        have hxa : x≠a := by intro he;subst x;exact hn hx
        simp [hxa]
      exact he.trans hf

theorem rebase_at_prefix (u v : List Op) (s : List α)
    (h : run (u++v) s=reflect s) :
    run (rebase u v) (run u s)=reflect (run u s) := by
  have hh : run v (run u s)=reflect s := by simpa [run_append] using h
  rw [rebase,run_append,hh,←reflect_run]

theorem rebase_same_root (u v : List Op) (s : List α)
    (hs : s.Nodup) (h : run (u++v) s=reflect s) :
    run (rebase u v) s=reflect s := by
  have hp := rebase_at_prefix u v s h
  have hperm := run_perm u s
  obtain ⟨f,hf⟩ := rename_exists (run u s) s (hperm.nodup_iff.mpr hs) hperm.length_eq
  have hm := congrArg (List.map f) hp
  rw [←run_map,←reflect_map,hf] at hm
  exact hm

theorem rot_mirror (w : List Op) : rotCount (mirror w)=rotCount w := by
  induction w with
  | nil => rfl
  | cons op w ih => cases op <;> simp [mirror,mirrorOp,rotCount] at ih ⊢ <;> exact ih

theorem rebase_prices (u v : List Op) :
    (rebase u v).length=(u++v).length ∧
    rotCount (rebase u v)=rotCount (u++v) := by
  constructor
  · simp [rebase,mirror,Nat.add_comm]
  · simp only [rebase,rot_append,rot_mirror,Nat.add_comm]

theorem actual_paid_rebase (u v : List Op) (s : List α)
    (hs : s.Nodup) (h : run (u++v) s=reflect s) :
    run (rebase u v) s=reflect s ∧
    (rebase u v).length=(u++v).length ∧
    rotCount (rebase u v)=rotCount (u++v) :=
  ⟨rebase_same_root u v s hs h,rebase_prices u v⟩

#print axioms rename_exists
#print axioms rebase_same_root
#print axioms rebase_prices
#print axioms actual_paid_rebase
end LRX.LowerBoundTwistedRebase
