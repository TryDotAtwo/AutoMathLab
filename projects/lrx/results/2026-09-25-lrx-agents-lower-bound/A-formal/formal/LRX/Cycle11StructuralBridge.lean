import LRX.Cycle11PairEncounter

namespace LRX.Cycle11StructuralBridge
open LRX.BlockExchange LRX.Cycle11TwoLabelRepair LRX.Cycle11PairEncounter
variable {α : Type*}

theorem step_perm (op : Op) (s : List α) : (step op s).Perm s := by
  cases op with
  | L => cases s with
    | nil => exact List.Perm.refl _
    | cons x t => simpa [step,left] using List.perm_append_comm t [x]
  | R =>
    have h : (left (right s)).Perm (right s) := by
      cases right s with
      | nil => exact List.Perm.refl _
      | cons x t => simpa [left] using List.perm_append_comm t [x]
    rw [LRX.ReducedPrice.left_right] at h
    exact h.symm
  | X => cases s with
    | nil => exact List.Perm.refl _
    | cons x s => cases s with
      | nil => exact List.Perm.refl _
      | cons y t => exact List.Perm.swap _ _ _

theorem run_perm (w : List Op) (s : List α) : (run w s).Perm s := by
  induction w generalizing s with
  | nil => exact List.Perm.refl _
  | cons op w ih => exact (ih (step op s)).trans (step_perm op s)

theorem map_fixed (f : α → α) (a b : α) (t : List α)
    (hf : ∀ x, x≠a → x≠b → f x=x) (ha : a∉t) (hb : b∉t) : t.map f=t := by
  calc
    t.map f = t.map id := List.map_congr_left (by
      intro x hx
      exact hf x (by intro h;subst x;exact ha hx) (by intro h;subst x;exact hb hx))
    _ = t := List.map_id t

theorem near_repair (f : α → α) (a b : α) (s : List α)
    (ha : f a=b) (hb : f b=a) (hf : ∀ x, x≠a → x≠b → f x=x)
    (hs : s.Nodup) (hn : Near a b s) :
    ∃ repair : List Op, repair.length≤3 ∧ run repair s=s.map f := by
  rcases hn with ⟨t,rfl⟩ | ⟨c,t,rfl⟩ | ⟨t,rfl⟩
  · simp only [List.nodup_cons,List.mem_cons,not_or] at hs
    exact ⟨[.X],by decide,repair_head f a b t ha hb (map_fixed f a b t hf hs.1.2 hs.2.1)⟩
  · simp only [List.nodup_cons,List.mem_cons,not_or] at hs
    exact ⟨[.L,.X,.R],by decide,repair_next f c a b t (hf c hs.1.1 hs.1.2.1)
      ha hb (map_fixed f a b t hf hs.2.1.2 hs.2.2.1)⟩
  · have hrot : (a::b::t).Nodup := by
      have h := (step_perm .R ((b::t)++[a])).nodup_iff.mpr hs
      simpa [step,right,left] using h
    simp only [List.nodup_cons,List.mem_cons,not_or] at hrot
    exact ⟨[.R,.X,.L],by decide,repair_wrap f a b t ha hb
      (map_fixed f a b t hf hrot.1.2 hrot.2.1)⟩

/-- The actual encounter is derived, not assumed. The two-point fiber endpoint
    is explicit; a separate quotient interface must establish that premise. -/
theorem structural_bridge (f : α → α) (a b : α) (w : List Op)
    (s target : List α) (hs : s.Nodup)
    (ha : f a=b) (hb : f b=a) (hf : ∀ x, x≠a → x≠b → f x=x)
    (hinv : (target.map f).map f=target)
    (hnot : ¬Pair a b s) (htarget : Pair a b (target.map f))
    (hend : run w s=target ∨ run w s=target.map f) :
    ∃ word : List Op, run word s=target ∧ word.length≤w.length+3 := by
  rcases hend with good | bad
  · exact ⟨w,good,by omega⟩
  · have hlast : Pair a b (run w s) := by rw [bad];exact htarget
    obtain ⟨u,v,hu,hn⟩ := first_encounter a b w s hnot hlast
    have hnd := (run_perm u s).nodup_iff.mpr hs
    obtain ⟨repair,hcost,hfix⟩ := near_repair f a b (run u s) ha hb hf hnd hn
    have hb' : run (u++v) s=target.map f := by rw [←hu];exact bad
    obtain ⟨word,hword,hlen⟩ := encounter_bridge f u v repair s target 3 hinv (Or.inr hb') hfix hcost
    exact ⟨word,hword,by simpa [←hu] using hlen⟩

#print axioms run_perm
#print axioms near_repair
#print axioms structural_bridge
end LRX.Cycle11StructuralBridge
