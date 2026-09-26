import UpperServiceInterface

/-! Recognition of the passive token at the contracted head. Local service
readiness only; does not establish target-cycle coverage or recursive service. -/
namespace LRX.UpperAffineBuffer

/-- Positive native index contracts to index minus one, with winding retained. -/
theorem contract_native_positive (M H i w : Int) (hM : 0 < M)
    (hi : 1 ≤ i) (hiM : i ≤ M) :
    contract M H (H+i+(M+1)*w) = H+(i-1)+M*w := by
  have he : H-(H+i+(M+1)*w)=(M+1-i)+(M+1)*(-w-1) := by ring
  unfold contract
  rw [he, Int.add_mul_ediv_left _ _ (by omega : M+1≠0),
    Int.ediv_eq_zero_of_lt (by omega : 0≤M+1-i) (by omega : M+1-i<M+1)]
  ring

/-- The distinguished native index zero contracts to the logical head class. -/
theorem contract_native_zero (M H w : Int) (hM : 0 < M) :
    contract M H (H+(M+1)*w) = H+M*w := by
  have he : H-(H+(M+1)*w)=(-w)*(M+1) := by ring
  unfold contract
  rw [he, Int.mul_ediv_cancel _ (by omega : M+1≠0)]
  ring
#print axioms contract_native_positive
#print axioms contract_native_zero
end LRX.UpperAffineBuffer

namespace LRX.UpperNativeLift
open LRX.UpperAffineBuffer
variable {α : Type*} [DecidableEq α]

/-- Among passive labels, logical head residue means exactly native index one.
This handles zero transport too: no distinct-position assumption is needed. -/
theorem passive_head_iff (a b : α) (ps : List α) (H : Int) (z : α → Int)
    (hn : (a::b::ps).Nodup)
    (h : Represents (ps.length+2) H (a::b::ps) z)
    (c : α) (hc : c∈a::b::ps) (hca : c≠a) :
    (contract ((ps.length:Int)+1) H (z c)-H)%((ps.length:Int)+1)=0 ↔ c=b := by
  obtain ⟨i,hi,hei⟩ := List.mem_iff_getElem.mp hc
  have hip : 1≤i := by
    by_contra hp
    have hz : i=0 := by omega
    subst i
    simp only [List.getElem_cons_zero] at hei
    exact hca hei.symm
  obtain ⟨w,hw⟩ := h i hi
  rw [hei] at hw
  have hiM : (i:Int)≤(ps.length:Int)+1 := by simp only [List.length_cons] at hi; omega
  have hv : contract ((ps.length:Int)+1) H (z c) = H+((i:Int)-1)+((ps.length:Int)+1)*w := by
    rw [hw]
    convert contract_native_positive ((ps.length:Int)+1) H (i:Int) w (by omega) (by omega) hiM using 1 <;> push_cast <;> ring
  have hr : (contract ((ps.length:Int)+1) H (z c)-H)%((ps.length:Int)+1)=(i:Int)-1 := by
    rw [hv]
    have he : H+((i:Int)-1)+((ps.length:Int)+1)*w-H=((i:Int)-1)+((ps.length:Int)+1)*w := by ring
    rw [he, Int.add_emod, Int.mul_emod_right, add_zero, Int.emod_emod,
      Int.emod_eq_of_lt (by omega : 0≤(i:Int)-1) (by omega : (i:Int)-1<(ps.length:Int)+1)]
  rw [hr]
  constructor
  · intro he
    have he1 : i=1 := by omega
    subst i
    simpa using hei.symm
  · intro hcb
    have hidx := hn.idxOf_getElem i hi
    rw [hei,hcb] at hidx
    have hbidx := hn.idxOf_getElem 1 (by simp)
    simp only [List.getElem_cons_succ,List.getElem_cons_zero] at hbidx
    rw [hbidx] at hidx
    omega
#print axioms passive_head_iff

/-- Readiness derived from the passive logical head class yields an actual paid
handoff to that label; target identity is a conclusion, not an endpoint axiom. -/
theorem paid_ready_handoff (a b : α) (ps : List α) (H : Int) (z : α → Int)
    (hn : (a::b::ps).Nodup)
    (h : Represents (ps.length+2) H (a::b::ps) z)
    (c : α) (hc : c∈a::b::ps) (hca : c≠a)
    (hready : (contract ((ps.length:Int)+1) H (z c)-H)%((ps.length:Int)+1)=0) :
    PaidEffect (ps.length+2) (a::b::ps) (c::a::ps) H H z
      (exchange a c z) [.X] (fun _ => 0) 1 := by
  have he := (passive_head_iff a b ps H z hn h c hc hca).mp hready
  subst c
  exact paid_handoff a b ps H z hn h
#print axioms paid_ready_handoff
end LRX.UpperNativeLift
