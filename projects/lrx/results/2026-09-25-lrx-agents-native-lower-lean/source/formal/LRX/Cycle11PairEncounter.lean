import LRX.Cycle11TwoLabelRepair
import LRX.ReducedPrice

namespace LRX.Cycle11PairEncounter
open LRX.BlockExchange
variable {α : Type*}

def edges (s : List α) : List (α × α) := List.zipWith Prod.mk s (left s)
def Pair (a b : α) (s : List α) : Prop := (a,b) ∈ edges s
def Near (a b : α) (s : List α) : Prop :=
  (∃ t, s=a::b::t) ∨ (∃ x t, s=x::a::b::t) ∨ (∃ t, s=(b::t)++[a])

theorem edges_left (s : List α) : edges (left s)=left (edges s) := by
  cases s with
  | nil => rfl
  | cons x s => cases s with
    | nil => rfl
    | cons y t =>
      simp only [edges,left,List.cons_append,List.nil_append,List.zipWith_cons_cons]
      have h := List.zipWith_append (f := Prod.mk) (l₁ := y::t) (l₂ := t++[x])
        (l₁' := [x]) (l₂' := [y]) (by simp)
      simpa [List.append_assoc] using h

theorem pair_left (a b : α) (s : List α) : Pair a b (left s) ↔ Pair a b s := by
  unfold Pair
  rw [edges_left]
  cases edges s <;> simp [left,or_comm]

theorem pair_right (a b : α) (s : List α) : Pair a b (right s) ↔ Pair a b s := by
  have h := pair_left a b (right s)
  rw [LRX.ReducedPrice.left_right] at h
  exact h.symm

theorem terminal_edge (a b z x y : α) (t : List α)
    (h : (a,b) ∈ List.zipWith Prod.mk (z::t) (t++[y])) :
    (a,b) ∈ List.zipWith Prod.mk (z::t) (t++[x]) ∨
      (∃ pre, z::t=pre++[a]) ∧ b=y := by
  induction t generalizing z with
  | nil =>
    simp only [List.nil_append,List.zipWith_cons_cons,List.zipWith_nil_left,List.mem_singleton,Prod.mk.injEq] at h
    exact Or.inr ⟨⟨[],by simp [h.1]⟩,h.2⟩
  | cons c t ih =>
    simp only [List.cons_append,List.zipWith_cons_cons,List.mem_cons] at h ⊢
    rcases h with h | h
    · exact Or.inl (Or.inl h)
    · rcases ih c h with old | ⟨⟨pre,hpre⟩,hb⟩
      · exact Or.inl (Or.inr old)
      · exact Or.inr ⟨⟨z::pre,by simp [hpre]⟩,hb⟩

theorem swap_birth (a b : α) (s : List α) (h : Pair a b (swap s)) :
    Pair a b s ∨ Near a b (swap s) := by
  cases s with
  | nil => exact Or.inl h
  | cons x s => cases s with
    | nil => exact Or.inl h
    | cons y t => cases t with
      | nil =>
        simp only [Pair,edges,swap,left,List.cons_append,List.nil_append,
          List.zipWith_cons_cons,List.zipWith_nil_left,List.mem_cons,List.not_mem_nil,or_false,
          Prod.mk.injEq] at h
        rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩
        · exact Or.inr (Or.inl ⟨[],by simp [swap,ha,hb]⟩)
        · exact Or.inl (by simp [Pair,edges,left,ha,hb])
      | cons z t =>
        simp only [Pair,edges,swap,left,List.cons_append,List.nil_append,
          List.zipWith_cons_cons,List.mem_cons] at h
        rcases h with h | h | h
        · have hh := Prod.mk.inj h
          exact Or.inr (Or.inl ⟨z::t,by simp [swap,hh.1,hh.2]⟩)
        · have hh := Prod.mk.inj h
          exact Or.inr (Or.inr (Or.inl ⟨y,t,by simp [swap,hh.1,hh.2]⟩))
        · rcases terminal_edge a b z x y t h with old | ⟨⟨pre,hpre⟩,hb⟩
          · exact Or.inl (by simp only [Pair,edges,left,List.cons_append,List.nil_append,
                List.zipWith_cons_cons,List.mem_cons];exact Or.inr (Or.inr old))
          · exact Or.inr (Or.inr (Or.inr ⟨x::pre,by simp [swap,←hpre,←hb]⟩))

theorem step_birth (a b : α) (op : Op) (s : List α)
    (h : Pair a b (step op s)) : Pair a b s ∨ Near a b (step op s) := by
  cases op with
  | L => exact Or.inl ((pair_left a b s).mp h)
  | R => exact Or.inl ((pair_right a b s).mp h)
  | X => exact swap_birth a b s h

/-- First creation of a directed cyclic adjacency forces an actual prefix encounter. -/
theorem first_encounter (a b : α) (w : List Op) (s : List α)
    (hnot : ¬Pair a b s) (hend : Pair a b (run w s)) :
    ∃ u v, w=u++v ∧ Near a b (run u s) := by
  induction w generalizing s with
  | nil => exact False.elim (hnot hend)
  | cons op w ih =>
    by_cases hfirst : Pair a b (step op s)
    · rcases step_birth a b op s hfirst with old | near
      · exact False.elim (hnot old)
      · exact ⟨[op],w,rfl,near⟩
    · obtain ⟨u,v,hu,hn⟩ := ih (step op s) hfirst hend
      exact ⟨op::u,v,by simp [hu],hn⟩

#print axioms pair_left
#print axioms pair_right
#print axioms swap_birth
#print axioms first_encounter
end LRX.Cycle11PairEncounter
