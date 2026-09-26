import LRX.LowerBoundSwapCount

/-! Filtered cyclic adjacency formulation of one-run color contiguity.
All events refer to the original actual LRX word. -/
namespace LRX.LowerBoundCyclicContiguity
open LRX.BlockExchange LRX.Cycle11PairEncounter LRX.Cycle11StructuralBridge
open LRX.LowerBoundNoRepeat LRX.LowerBoundPairParity LRX.LowerBoundSwapCount
variable {α : Type*} [DecidableEq α]

def keepPair (color : α → Bool) (a b x : α) : Bool :=
  decide (x=a ∨ x=b ∨ color x≠color a)

def Separated (a b : α) (s : List α) : Prop := ¬Pair a b s ∧ ¬Pair b a s

def MonoTrace (color : α → Bool) (w : List Op) (s : List α) : Prop :=
  ∀ u v a b, w=u++[.X]++v → HeadPair a b (run u s) → color a=color b

theorem pair_head (a b : α) (t : List α) : Pair a b (a::b::t) := by
  simp [Pair,edges,left]

theorem near_false (a b x y : α) (t : List α)
    (hxa : x≠a) (hxb : x≠b) (hya : y≠a) : ¬Near a b (x::y::t) := by
  intro h
  rcases h with ⟨v,hv⟩ | ⟨z,v,hv⟩ | ⟨v,hv⟩
  · exact hxa (List.cons.inj hv).1
  · exact hya (List.cons.inj (List.cons.inj hv).2).1
  · simp only [List.cons_append] at hv
    exact hxb (List.cons.inj hv).1

theorem separated_swap_away (a b x y : α) (t : List α)
    (hxa : x≠a) (hxb : x≠b) (hya : y≠a) (hyb : y≠b)
    (h : Separated a b (x::y::t)) : Separated a b (y::x::t) := by
  constructor
  · intro hp
    rcases swap_birth a b (x::y::t) hp with old | near
    · exact h.1 old
    · exact near_false a b y x t hya hyb hxa near
  · intro hp
    rcases swap_birth b a (x::y::t) hp with old | near
    · exact h.2 old
    · exact near_false b a y x t hyb hya hxb near

theorem filtered_pair_left (keep : α → Bool) (a b : α) (s : List α) :
    Pair a b ((left s).filter keep) ↔ Pair a b (s.filter keep) := by
  cases s with
  | nil => rfl
  | cons x xs =>
    cases hx : keep x with
    | false => simp [left,hx]
    | true => simpa [left,hx] using pair_left a b (x::xs.filter keep)

theorem filtered_pair_right (keep : α → Bool) (a b : α) (s : List α) :
    Pair a b ((right s).filter keep) ↔ Pair a b (s.filter keep) := by
  have h := filtered_pair_left keep a b (right s)
  rw [LRX.ReducedPrice.left_right] at h
  exact h.symm

theorem filtered_head_not_separated (color : α → Bool) (a b : α) (s : List α)
    (hp : HeadPair a b s) : ¬Separated a b (s.filter (keepPair color a b)) := by
  intro hs
  rcases hp with ⟨t,rfl⟩ | ⟨t,rfl⟩
  · apply hs.1
    simpa [keepPair] using pair_head a b (t.filter (keepPair color a b))
  · apply hs.2
    simpa [keepPair] using pair_head b a (t.filter (keepPair color a b))

theorem filtered_separated_swap (color : α → Bool) (a b x y : α) (t : List α)
    (hab : color a=color b) (hxy : color x=color y)
    (h : Separated a b ((x::y::t).filter (keepPair color a b))) :
    Separated a b ((y::x::t).filter (keepPair color a b)) := by
  by_cases hx : x=a ∨ x=b
  · by_cases hy : y=a ∨ y=b
    · rcases hx with hxa | hxb <;> rcases hy with hya | hyb
      · subst x; subst y; exact h
      · subst x; subst y
        exact False.elim (filtered_head_not_separated color a b (a::b::t) (Or.inl ⟨t,rfl⟩) h)
      · subst x; subst y
        exact False.elim (filtered_head_not_separated color a b (b::a::t) (Or.inr ⟨t,rfl⟩) h)
      · subst x; subst y; exact h
    · have hky : keepPair color a b y=false := by
        rcases hx with rfl | rfl <;> simp_all [keepPair]
      have hkx : keepPair color a b x=true := by rcases hx with rfl | rfl <;> simp [keepPair]
      simpa [hkx,hky] using h
  · by_cases hy : y=a ∨ y=b
    · have hkx : keepPair color a b x=false := by
        rcases hy with rfl | rfl <;> simp_all [keepPair]
      have hky : keepPair color a b y=true := by rcases hy with rfl | rfl <;> simp [keepPair]
      simpa [hkx,hky] using h
    · have he : keepPair color a b x=keepPair color a b y := by
        have hx' := not_or.mp hx
        have hy' := not_or.mp hy
        simp [keepPair,hx'.1,hx'.2,hy'.1,hy'.2,hxy]
      cases hkx : keepPair color a b x with
      | false =>
        have hky : keepPair color a b y=false := he.symm.trans hkx
        simpa [hkx,hky] using h
      | true =>
        have hky : keepPair color a b y=true := he.symm.trans hkx
        have ht : Separated a b (x::y::t.filter (keepPair color a b)) := by simpa [hkx,hky] using h
        have hxa : x≠a := fun h => hx (Or.inl h)
        have hxb : x≠b := fun h => hx (Or.inr h)
        have hya : y≠a := fun h => hy (Or.inl h)
        have hyb : y≠b := fun h => hy (Or.inr h)
        simpa [hkx,hky] using separated_swap_away a b x y _ hxa hxb hya hyb ht


theorem mono_tail (color : α → Bool) (op : Op) (w : List Op) (s : List α)
    (h : MonoTrace color (op::w) s) : MonoTrace color w (step op s) := by
  intro u v a b hw hp
  apply h (op::u) v a b
  · simp [hw]
  · simpa [run] using hp

theorem filtered_separated_step (color : α → Bool) (a b : α) (op : Op) (s : List α)
    (hab : color a=color b)
    (hallowed : op=Op.X → ∀ x y t, s=x::y::t → color x=color y)
    (hs : Separated a b (s.filter (keepPair color a b))) :
    Separated a b ((step op s).filter (keepPair color a b)) := by
  cases op with
  | L =>
    exact ⟨fun h => hs.1 ((filtered_pair_left _ a b s).mp h),
      fun h => hs.2 ((filtered_pair_left _ b a s).mp h)⟩
  | R =>
    exact ⟨fun h => hs.1 ((filtered_pair_right _ a b s).mp h),
      fun h => hs.2 ((filtered_pair_right _ b a s).mp h)⟩
  | X =>
    cases s with
    | nil => exact hs
    | cons x s => cases s with
      | nil => exact hs
      | cons y t => exact filtered_separated_swap color a b x y t hab (hallowed rfl x y t rfl) hs

theorem separated_mono_count_zero (color : α → Bool) (a b : α) (w : List Op) (s : List α)
    (hab : color a=color b) (hm : MonoTrace color w s)
    (hs : Separated a b (s.filter (keepPair color a b))) :
    swapCount a b w s=0 := by
  induction w generalizing s with
  | nil => rfl
  | cons op w ih =>
    have ha : op=Op.X → ∀ x y t, s=x::y::t → color x=color y := by
      intro hop x y t heq
      subst op
      exact hm [] w x y rfl (Or.inl ⟨t,heq⟩)
    have hs' := filtered_separated_step color a b op s hab ha hs
    have hz := ih (step op s) (mono_tail color op w s hm) hs'
    have he : swapEvent a b op s=false := by
      cases hh : swapEvent a b op s with
      | false => rfl
      | true =>
        obtain ⟨hop,hp⟩ := event_true a b op s hh
        exact False.elim (filtered_head_not_separated color a b s hp hs)
    simp [swapCount,he,hz]

theorem event_count_pos (a b : α) (u v : List Op) (s : List α)
    (hp : HeadPair a b (run u s)) : 0<swapCount a b (u++[.X]++v) s := by
  induction u generalizing s with
  | nil =>
    have he : swapEvent a b .X s=true := (pairAtHead_true a b s).mpr hp
    simp [swapCount,he]
  | cons op u ih =>
    have hh := ih (step op s) hp
    simp only [List.cons_append,swapCount]
    omega

theorem counts_mono (color : α → Bool) (w : List Op) (s : List α)
    (hs : s.Nodup)
    (hc : ∀ a b : α, a≠b → swapCount a b w s=if color a=color b then 1 else 0) :
    MonoTrace color w s := by
  intro u v a b hw hp
  have hn := (run_perm u s).nodup_iff.mpr hs
  have hne : a≠b := by
    intro he
    subst b
    rcases hp with ⟨t,ht⟩ | ⟨t,ht⟩ <;> rw [ht] at hn <;> simp at hn
  have hcount := hc a b hne
  have hpos : 0<swapCount a b w s := by
    rw [hw]
    exact event_count_pos a b u v s hp
  by_contra he
  simp [he] at hcount
  omega

/-- Pairwise cyclic contiguity: after deleting every other same-color label,
any two distinct labels of that color are cyclic neighbors. This criterion
excludes two distinct color runs separated in both directions by other colors.
All count and trace hypotheses are derived from shortestness and reflection. -/
theorem shortest_reflection_contiguity (w v : List Op) (s : List α) (z : α)
    (hs : s.Nodup) (hall : ∀ a : α, a∈s) (hmin : Shortest w s)
    (hv : Rotations v) (hend : run w s=run v s.reverse) :
    ∃ color : α → Bool,
      (∀ a b : α, a≠b → swapCount a b w s=if color a=color b then 1 else 0) ∧
      (∀ a b : α, a≠b → color a=color b →
        Pair a b (s.filter (keepPair color a b)) ∨ Pair b a (s.filter (keepPair color a b))) := by
  obtain ⟨color,hc⟩ := shortest_reflection_counts w v s z hs hall hmin hv hend
  have hm := counts_mono color w s hs hc
  refine ⟨color,hc,?_⟩
  intro a b hab he
  by_contra hnot
  have hsep : Separated a b (s.filter (keepPair color a b)) :=
    ⟨fun h => hnot (Or.inl h),fun h => hnot (Or.inr h)⟩
  have hz := separated_mono_count_zero color a b w s he hm hsep
  have hcount := hc a b hab
  simp [he] at hcount
  omega

#print axioms filtered_separated_swap
#print axioms separated_mono_count_zero
#print axioms counts_mono
#print axioms shortest_reflection_contiguity
end LRX.LowerBoundCyclicContiguity
