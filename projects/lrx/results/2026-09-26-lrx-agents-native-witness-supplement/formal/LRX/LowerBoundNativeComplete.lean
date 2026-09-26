import LRX.LowerBoundNativeTrace
import LRX.LowerBoundExceptionalEndpoint

/-! Composition of A's native physical reduction and B's exceptional cases.
All hypotheses of the exported word lower bound are native endpoint facts. -/
namespace LRX.LowerBoundNativeComplete
open LRX.BlockExchange LRX.LowerBoundNativeTrace
open LRX.LowerBoundExceptionalNative LRX.LowerBoundNoRepeat
open LRX.Cycle11StructuralBridge LRX.Cycle11WordSymmetry

variable {α : Type*} [DecidableEq α] [Fintype α] {a b : Nat}

theorem indexed_false_card (e : Label a b ≃ α) :
    (colorClass (fun z => color (e.symm z)) false).card=a := by
  have he : Finset.univ.image (fun x : Fin a => e (.inl x))=
      colorClass (fun z => color (e.symm z)) false := by
    ext z
    simp only [Finset.mem_image,Finset.mem_univ,true_and,colorClass,Finset.mem_filter,true_and]
    constructor
    · rintro ⟨x,rfl⟩; simp [color]
    · intro h
      cases hz : e.symm z with
      | inl x =>
        refine ⟨x,?_⟩
        have hh := congrArg e hz
        simpa only [Equiv.apply_symm_apply] using hh.symm
      | inr y => simp [hz,color] at h
  rw [←he,Finset.card_image_of_injective _ (by
    intro x y h; exact Sum.inl.inj (e.injective h))]
  simp

theorem indexed_true_card (e : Label a b ≃ α) :
    (colorClass (fun z => color (e.symm z)) true).card=b := by
  have he : Finset.univ.image (fun x : Fin b => e (.inr x))=
      colorClass (fun z => color (e.symm z)) true := by
    ext z
    simp only [Finset.mem_image,Finset.mem_univ,true_and,colorClass,Finset.mem_filter,true_and]
    constructor
    · rintro ⟨x,rfl⟩; simp [color]
    · intro h
      cases hz : e.symm z with
      | inl x => simp [hz,color] at h
      | inr y =>
        refine ⟨y,?_⟩
        have hh := congrArg e hz
        simpa only [Equiv.apply_symm_apply] using hh.symm
  rw [←he,Finset.card_image_of_injective _ (by
    intro x y h; exact Sum.inr.inj (e.injective h))]
  simp

omit [DecidableEq α] [Fintype α] in
theorem reflect_eq_reverse_rotate (xs : List α) (hn : 2≤xs.length) :
    reflect xs=xs.reverse.rotate (xs.length-2) := by
  rw [reflect_as_reverse]
  change right (right xs.reverse)=_
  have hr : (right xs.reverse).length=xs.length := by
    have hh := (step_perm .R xs.reverse).length_eq
    simpa only [step,List.length_reverse] using hh
  rw [right_rotate _ (by omega),hr,right_rotate _ (by simp; omega),List.length_reverse,List.rotate_rotate]
  have he : xs.length-1+(xs.length-1)=(xs.length-2)+xs.reverse.length := by simp; omega
  rw [he,←List.rotate_rotate]
  simpa only [List.length_rotate] using List.rotate_length (xs.reverse.rotate (xs.length-2))

/-- Full native-word lower bound for the specified distinct-label target,
with unit cost for every L/R/X and no structural or physical hypotheses. -/
theorem native_lower {n : Nat} (hn : 4≤n) (w : List Op)
    (hend : run w (root n)=target n) : n*(n-1)/2≤w.length := by
  have ht : target n=reflect (root n) := by
    simpa [target,root] using (reflect_eq_reverse_rotate (root n) (by simp [root]; omega)).symm
  obtain ⟨v,a,b,e,s,hlen,hmin,he,hnlen,hrep,hsA,hsB,hcounts,hm,hend',htrace,hlow⟩ :=
    native_physical_reduction w (root n) ⟨0,by omega⟩
      (List.nodup_finRange n) (fun x => List.mem_finRange x) (hend.trans ht)
  let c : Fin n → Bool := fun x => color (e.symm x)
  have hc : ∀ x y : Fin n,x≠y → LRX.LowerBoundSwapCount.swapCount x y v (root n)=
      if c x=c y then 1 else 0 := by
    intro x y hxy
    have hh := hcounts (e.symm x) (e.symm y) (fun hh => hxy (e.symm.injective hh))
    simpa only [Equiv.apply_symm_apply,c] using hh
  have hv : run v (root n)=target n := he.trans hend
  by_cases ha : 2≤a
  · by_cases hb : 2≤b
    · simpa [root] using hlow ha hb
    · have hs : (colorClass c true).card≤1 := by
        rw [indexed_true_card e]; omega
      exact (shortest_exceptional_native_lower hn v hmin hv c true hc hs).trans hlen
  · have hs : (colorClass c false).card≤1 := by
      rw [indexed_false_card e]; omega
    exact (shortest_exceptional_native_lower hn v hmin hv c false hc hs).trans hlen

#print axioms indexed_false_card
#print axioms indexed_true_card
#print axioms reflect_eq_reverse_rotate
#print axioms native_lower
end LRX.LowerBoundNativeComplete
