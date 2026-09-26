import UpperTransport
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

/-! Paid service interface and missing buffer handoff. No recursive existence. -/
namespace LRX.UpperAffineBuffer

/-- The two physical slots glued by contraction have the same integer logical
coordinate even at arbitrary winding. -/
theorem contract_glued_slots (M H w : Int) (hM : 0 < M) :
    contract M H (H+(M+1)*w+1) = contract M H (H+(M+1)*w) := by
  have h0 : H-(H+(M+1)*w)=(-w)*(M+1) := by ring
  have h1 : H-(H+(M+1)*w+1)=M+(M+1)*(-w-1) := by ring
  unfold contract
  rw [h0, h1, Int.mul_ediv_cancel _ (by omega : M+1≠0),
    Int.add_mul_ediv_left _ _ (by omega : M+1≠0),
    Int.ediv_eq_zero_of_lt (by omega : 0≤M) (by omega : M<M+1)]
  ring
#print axioms contract_glued_slots
end LRX.UpperAffineBuffer

namespace LRX.UpperNativeLift
open LRX.BlockExchange
open LRX.UpperAffineBuffer (contract contract_glued_slots)
variable {α : Type*} [DecidableEq α]

/-- A single paid X changes buffer identity but no integer logical coordinate.
Unlike a free frame change this is tied to the exact native exchange. -/
theorem handoff_logical (a b : α) (ps : List α) (H : Int) (z : α → Int)
    (hn : (a::b::ps).Nodup)
    (h : Represents (ps.length+2) H (a::b::ps) z) (c : α) :
    contract ((ps.length:Int)+1) H (exchange a b z c) =
      contract ((ps.length:Int)+1) H (z c) := by
  have hab : a≠b := by intro he; exact (List.nodup_cons.mp hn).1 (by simp [he])
  obtain ⟨wa,hwa⟩ := h 0 (by simp)
  obtain ⟨wb,hwb⟩ := h 1 (by simp)
  simp only [List.getElem_cons_zero, Nat.cast_zero, add_zero] at hwa
  simp only [List.getElem_cons_succ, List.getElem_cons_zero, Nat.cast_one] at hwb
  by_cases ha : c=a
  · subst c
    simp only [exchange, if_pos rfl]
    rw [hwa]
    convert contract_glued_slots ((ps.length:Int)+1) H wa (by omega) using 1 <;> push_cast <;> ring
  · by_cases hb : c=b
    · subst c
      simp only [exchange, if_neg ha, if_pos rfl]
      rw [hwb]
      convert (contract_glued_slots ((ps.length:Int)+1) H wb (by omega)).symm using 1 <;> push_cast <;> ring
    · simp [exchange,ha,hb]

/-- A composable certificate for an actual paid native word. Endpoint lift and
logical effects are obligations, not automatic claims of service existence. -/
structure PaidEffect (n : Nat) (xs xs' : List α) (H H' : Int)
    (z z' : α → Int) (word : List Op) (delta : α → Int) (cost : Nat) : Prop where
  endpoint : run word xs = xs'
  represented : Represents n H' xs' z'
  logical : ∀ c, contract ((n:Int)-1) H' (z' c) =
    contract ((n:Int)-1) H (z c) + delta c
  paid : word.length = cost

/-- Exact composition; every native letter remains paid and integer winding
is retained. This theorem consumes certificates; it does not assume them away. -/
theorem PaidEffect.append {n : Nat} {xs ys zs : List α} {H K J : Int}
    {z u v : α → Int} {w w' : List Op} {d e : α → Int} {c c' : Nat}
    (h : PaidEffect n xs ys H K z u w d c)
    (h' : PaidEffect n ys zs K J u v w' e c') :
    PaidEffect n xs zs H J z v (w++w') (fun a => d a+e a) (c+c') := by
  refine ⟨?_,h'.represented,?_,?_⟩
  · rw [run_append,h.endpoint,h'.endpoint]
  · intro a
    rw [h'.logical,h.logical]
    omega
  · simp [h.paid,h'.paid]

/-- Nonvacuous handoff certificate, exact cost one, no zero-winding restriction. -/
theorem paid_handoff (a b : α) (ps : List α) (H : Int) (z : α → Int)
    (hn : (a::b::ps).Nodup)
    (h : Represents (ps.length+2) H (a::b::ps) z) :
    PaidEffect (ps.length+2) (a::b::ps) (b::a::ps) H H z
      (exchange a b z) [.X] (fun _ => 0) 1 := by
  refine ⟨rfl,step_X a b ps H z hn h,?_,rfl⟩
  intro c
  have he : ((ps.length+2:Nat):Int)-1=(ps.length:Int)+1 := by omega
  rw [he,add_zero]
  exact handoff_logical a b ps H z hn h c

/-- Outside-label invariance follows from an explicitly supported effect. -/
theorem PaidEffect.outside {n : Nat} {xs ys : List α} {H K : Int}
    {z u : α → Int} {w : List Op} {d : α → Int} {cost : Nat}
    (h : PaidEffect n xs ys H K z u w d cost) (a : α) (ha : d a=0) :
    contract ((n:Int)-1) K (u a)=contract ((n:Int)-1) H (z a) := by
  simpa [ha] using h.logical a

#print axioms handoff_logical
#print axioms PaidEffect.append
#print axioms paid_handoff
#print axioms PaidEffect.outside
/-- The existing constructive transport inhabits the paid interface. -/
theorem paid_forward (k : Nat) (a : α) (ps : List α) (H : Int) (z : α → Int)
    (hne : 1≤ps.length) (hall : ∀ c, c∈a::ps) (hn : (a::ps).Nodup)
    (h : Represents (ps.length+1) H (a::ps) z) :
    ∃ z', PaidEffect (ps.length+1) (a::ps)
      (run (LRX.UpperBufferNative.forward k) (a::ps)) H (H+(k:Int)) z z'
      (LRX.UpperBufferNative.forward k) (fun c => if c=a then (k:Int) else 0) (2*k) := by
  obtain ⟨z',hr,hl⟩ := forward_transport k a ps H z hne hall hn h
  refine ⟨z',rfl,hr,?_,LRX.UpperBufferNative.forward_length k⟩
  intro c
  have he : ((ps.length+1:Nat):Int)-1=(ps.length:Int) := by omega
  rw [he]
  exact hl c

theorem paid_backward (k : Nat) (a : α) (ps : List α) (H : Int) (z : α → Int)
    (hne : 1≤ps.length) (hall : ∀ c, c∈a::ps) (hn : (a::ps).Nodup)
    (h : Represents (ps.length+1) H (a::ps) z) :
    ∃ z', PaidEffect (ps.length+1) (a::ps)
      (run (LRX.UpperBufferNative.backward k) (a::ps)) H (H-(k:Int)) z z'
      (LRX.UpperBufferNative.backward k) (fun c => -(if c=a then (k:Int) else 0)) (2*k) := by
  obtain ⟨z',hr,hl⟩ := backward_transport k a ps H z hne hall hn h
  refine ⟨z',rfl,hr,?_,LRX.UpperBufferNative.backward_length k⟩
  intro c
  have he : ((ps.length+1:Nat):Int)-1=(ps.length:Int) := by omega
  rw [he]
  simpa [sub_eq_add_neg] using hl c

/-- Target interface for a RETURNING child service, not an existence theorem.
The root open procedure has a different endpoint and must not use this type.
Cycle set must contain ALL descendants; labels is their full support. -/
structure SubtreeService {κ : Type*} (n : Nat) (cycles : Finset κ)
    (winding : κ → Int) (labels : Finset α) (tau : α → Int)
    (incoming : α) (ps ps' : List α) (H H' : Int) (z z' : α → Int)
    (word : List Op) (cost : Nat) : Prop where
  effect : PaidEffect n (incoming::ps) (incoming::ps') H H' z z' word
    (fun a => if a∈labels then tau a else 0) cost
  frame : H'=H+((n:Int)-1)*(∑ c∈cycles, winding c)
  parent_outside : incoming∉labels

/-- The incoming parent's integer logical coordinate is restored even when
its physical coordinate is not: a wound child need not close physically. -/
theorem SubtreeService.parent_logical {κ : Type*} {n : Nat} {cycles : Finset κ}
    {winding : κ → Int} {labels : Finset α} {tau : α → Int}
    {incoming : α} {ps ps' : List α} {H H' : Int} {z z' : α → Int}
    {word : List Op} {cost : Nat}
    (h : SubtreeService n cycles winding labels tau incoming ps ps' H H' z z' word cost) :
    contract ((n:Int)-1) H' (z' incoming)=contract ((n:Int)-1) H (z incoming) := by
  apply h.effect.outside
  simp [h.parent_outside]

#print axioms paid_forward
#print axioms paid_backward
#print axioms SubtreeService.parent_logical
end LRX.UpperNativeLift
