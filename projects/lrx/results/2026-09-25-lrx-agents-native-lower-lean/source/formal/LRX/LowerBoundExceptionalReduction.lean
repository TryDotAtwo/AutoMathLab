import LRX.LowerBoundExceptionalNative

/-! Complete exceptional-case gate for an arbitrary native word.
The remaining two-large-arc geometry is A's LB-L1 responsibility. -/
namespace LRX.LowerBoundExceptionalReduction
open LRX.BlockExchange LRX.LowerBoundNoRepeat LRX.LowerBoundSwapCount
open LRX.LowerBoundPairParity LRX.LowerBoundCyclicContiguity
open LRX.LowerBoundExceptionalNative LRX.Cycle11PairEncounter
variable {α : Type*} [DecidableEq α]

theorem exists_shortest_le (w : List Op) (s : List α) :
    ∃ v : List Op, run v s=run w s ∧ Shortest v s ∧ v.length≤w.length := by
  classical
  have hex : ∃ k : Nat, ∃ v : List Op, run v s=run w s ∧ v.length=k :=
    ⟨w.length,w,rfl,rfl⟩
  obtain ⟨v,hend,hlen⟩ := Nat.find_spec hex
  have hm : Shortest v s := by
    intro u hu
    have hh := Nat.find_min' hex (m := u.length) ⟨u,hu.trans hend,rfl⟩
    omega
  exact ⟨v,hend,hm,hm w hend.symm⟩

theorem run_left_replicate (k : Nat) (s : List α) :
    run (List.replicate k Op.L) s=s.rotate k := by
  induction k generalizing s with
  | zero => simp [run]
  | succ k ih =>
    have hl : left s=s.rotate 1 := by cases s <;> simp [left]
    simp only [List.replicate_succ, run, step, ih, hl, List.rotate_rotate]
    congr 1 <;> omega

theorem left_replicate_rotations (k : Nat) : Rotations (List.replicate k Op.L) := by
  intro op hop
  have he := (List.mem_replicate.mp hop).2
  rw [he]
  intro h
  cases h

theorem flip_class [Fintype α] (color : α → Bool) (c : Bool) :
    colorClass (fun x => !(color x)) c=colorClass color (!c) := by
  ext x
  cases hx : color x <;> cases c <;> simp [colorClass, hx]

theorem flip_counts (color : α → Bool) (w : List Op) (s : List α)
    (hc : ∀ a b : α, a≠b → swapCount a b w s=if color a=color b then 1 else 0) :
    ∀ a b : α, a≠b → swapCount a b w s=if !(color a)=!(color b) then 1 else 0 := by
  intro a b hab
  simpa using hc a b hab

theorem shortest_small_class_either_order {n : Nat} (hn : 4≤n)
    (w : List Op) (hmin : Shortest w (root n)) (hend : run w (root n)=target n)
    (color : Fin n → Bool)
    (hc : ∀ a b : Fin n, a≠b →
      swapCount a b w (root n)=if color a=color b then 1 else 0)
    (hsmall : (colorClass color false).card≤1 ∨ (colorClass color true).card≤1) :
    n*(n-1)/2≤w.length := by
  rcases hsmall with h | h
  · exact shortest_exceptional_native_lower hn w hmin hend color false hc h
  · exact shortest_exceptional_native_lower hn w hmin hend color true hc h

/-- For every hypothetical short original word, shortestness, actual pair
counts, monochromatic swaps, cyclic contiguity, and BOTH class sizes≥2
are derived. No exceptional-class or parity hypothesis is left to A. -/
theorem short_native_word_two_large_classes {n : Nat} (hn : 4≤n)
    (w : List Op) (hend : run w (root n)=target n) (hshort : w.length<n*(n-1)/2) :
    ∃ (v : List Op) (color : Fin n → Bool),
      run v (root n)=target n ∧ Shortest v (root n) ∧ v.length≤w.length ∧
      (∀ a b : Fin n, a≠b →
        swapCount a b v (root n)=if color a=color b then 1 else 0) ∧
      MonoTrace color v (root n) ∧
      2≤(colorClass color false).card ∧ 2≤(colorClass color true).card ∧
      (∀ a b : Fin n, a≠b → color a=color b →
        Pair a b ((root n).filter (keepPair color a b)) ∨
        Pair b a ((root n).filter (keepPair color a b))) := by
  obtain ⟨v,hv,hmin,hle⟩ := exists_shortest_le w (root n)
  have he : run v (root n)=target n := hv.trans hend
  have hreflection : run v (root n)=run (List.replicate (n-2) Op.L) (root n).reverse := by
    rw [run_left_replicate]
    exact he
  obtain ⟨color,hc,hcont⟩ := shortest_reflection_contiguity v
    (List.replicate (n-2) Op.L) (root n) ⟨0,by omega⟩
    (List.nodup_finRange n) (fun a => List.mem_finRange a) hmin
    (left_replicate_rotations (n-2)) hreflection
  have hlarge : ∀ c, 2≤(colorClass color c).card := by
    intro c
    by_contra hh
    have hs : (colorClass color c).card≤1 := by omega
    have hb := shortest_exceptional_native_lower hn v hmin he color c hc hs
    omega
  exact ⟨v,color,he,hmin,hle,hc,counts_mono color v (root n)
    (List.nodup_finRange n) hc,hlarge false,hlarge true,hcont⟩

#print axioms exists_shortest_le
#print axioms flip_class
#print axioms flip_counts
#print axioms shortest_small_class_either_order
#print axioms short_native_word_two_large_classes
end LRX.LowerBoundExceptionalReduction
