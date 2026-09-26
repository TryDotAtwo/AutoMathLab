import UpperNativeState

/-! Exact contracted-coordinate updates. Local paid-macro bridge, not service. -/
namespace LRX.UpperAffineBuffer

/-- The distinguished buffer advances with the physical frame, including winding. -/
theorem contract_shift (M H z d : Int) :
    contract M (H+d) (z+d) = contract M H z+d := by
  unfold contract
  have he : H+d-(z+d)=H-z := by ring
  rw [he]
  ring

/-- Forward paid macro: the passive neighbour moves physically backwards,
but stays at its logical coordinate. n=M+1>=2 includes the n=2 seam. -/
theorem contract_forward_neighbor (M H z : Int) (hM : 0<M)
    (hr : (H-z)%(M+1)=M) :
    contract M (H+1) (z-1)=contract M H z := by
  have he := Int.emod_add_mul_ediv (H-z) (M+1)
  rw [hr] at he
  have hx : H+1-(z-1)=1+(M+1)*((H-z)/(M+1)+1) := by nlinarith
  have hd : (H+1-(z-1))/(M+1)=(H-z)/(M+1)+1 := by
    rw [hx, Int.add_mul_ediv_left _ _ (by omega : M+1≠0)]
    rw [Int.ediv_eq_zero_of_lt (by omega) (by omega)]
    omega
  unfold contract
  rw [hd]
  omega

/-- All other physical coordinates stay put under the forward frame shift. -/
theorem contract_forward_other (M H z : Int) (hM : 0<M)
    (hr : (H-z)%(M+1)≠M) :
    contract M (H+1) z=contract M H z := by
  have he := Int.emod_add_mul_ediv (H-z) (M+1)
  have hlo := Int.emod_nonneg (H-z) (by omega : M+1≠0)
  have hhi := Int.emod_lt_of_pos (H-z) (by omega : 0<M+1)
  have hx : H+1-z=((H-z)%(M+1)+1)+(M+1)*((H-z)/(M+1)) := by nlinarith
  have hd : (H+1-z)/(M+1)=(H-z)/(M+1) := by
    rw [hx, Int.add_mul_ediv_left _ _ (by omega : M+1≠0)]
    rw [Int.ediv_eq_zero_of_lt (by omega) (by omega)]
    omega
  unfold contract
  rw [hd]

/-- Backward paid macro: the passive neighbour stays logical despite +1 physical. -/
theorem contract_backward_neighbor (M H z : Int) (hM : 0<M)
    (hr : (H-z)%(M+1)=1) :
    contract M (H-1) (z+1)=contract M H z := by
  have he := Int.emod_add_mul_ediv (H-z) (M+1)
  rw [hr] at he
  have hx : H-1-(z+1)=M+(M+1)*((H-z)/(M+1)-1) := by nlinarith
  have hd : (H-1-(z+1))/(M+1)=(H-z)/(M+1)-1 := by
    rw [hx, Int.add_mul_ediv_left _ _ (by omega : M+1≠0)]
    rw [Int.ediv_eq_zero_of_lt (by omega) (by omega)]
    omega
  unfold contract
  rw [hd]
  omega

/-- Non-head coordinates do not change logically under a backward frame shift. -/
theorem contract_backward_other (M H z : Int) (hM : 0<M)
    (hr : (H-z)%(M+1)≠0) :
    contract M (H-1) z=contract M H z := by
  have he := Int.emod_add_mul_ediv (H-z) (M+1)
  have hlo := Int.emod_nonneg (H-z) (by omega : M+1≠0)
  have hhi := Int.emod_lt_of_pos (H-z) (by omega : 0<M+1)
  have hx : H-1-z=((H-z)%(M+1)-1)+(M+1)*((H-z)/(M+1)) := by nlinarith
  have hd : (H-1-z)/(M+1)=(H-z)/(M+1) := by
    rw [hx, Int.add_mul_ediv_left _ _ (by omega : M+1≠0)]
    rw [Int.ediv_eq_zero_of_lt (by omega) (by omega)]
    omega
  unfold contract
  rw [hd]

#print axioms contract_shift
#print axioms contract_forward_neighbor
#print axioms contract_forward_other
#print axioms contract_backward_neighbor
#print axioms contract_backward_other

variable {α : Type*} [DecidableEq α]
open LRX.UpperNativeLift (exchange)

/-- Full-label forward update: exactly the distinguished label gains one. -/
theorem logical_forward (M H : Int) (z : α → Int) (a b : α)
    (hM : 0<M) (hab : a≠b)
    (hinj : Function.Injective fun c => (H-z c)%(M+1))
    (hb : (H-z b)%(M+1)=M) (c : α) :
    contract M (H+1) (exchange a b z c)=contract M H (z c)+(if c=a then 1 else 0) := by
  by_cases ha : c=a
  · subst c
    simp only [exchange, if_pos rfl]
    exact contract_shift M H (z a) 1
  · by_cases hc : c=b
    · subst c
      simp only [exchange, if_neg ha, if_pos rfl, add_zero]
      exact contract_forward_neighbor M H (z b) hM hb
    · have hr : (H-z c)%(M+1)≠M := by
        intro he
        exact hc (hinj (he.trans hb.symm))
      simp only [exchange, if_neg ha, if_neg hc, add_zero]
      exact contract_forward_other M H (z c) hM hr

/-- Full-label backward update: exactly the distinguished label loses one. -/
theorem logical_backward (M H : Int) (z : α → Int) (a b : α)
    (hM : 0<M) (hab : a≠b)
    (hinj : Function.Injective fun c => (H-z c)%(M+1))
    (ha : (H-z a)%(M+1)=0) (hb : (H-z b)%(M+1)=1) (c : α) :
    contract M (H-1) (exchange b a z c)=contract M H (z c)-(if c=a then 1 else 0) := by
  by_cases hc : c=a
  · subst c
    simp only [exchange, if_neg hab, if_pos rfl]
    simpa [sub_eq_add_neg] using contract_shift M H (z a) (-1)
  · by_cases hd : c=b
    · subst c
      simp only [exchange, if_pos rfl, if_neg hc, sub_zero]
      exact contract_backward_neighbor M H (z b) hM hb
    · have hr : (H-z c)%(M+1)≠0 := by
        intro he
        exact hc (hinj (he.trans ha.symm))
      simp only [exchange, if_neg hd, if_neg hc, sub_zero]
      exact contract_backward_other M H (z c) hM hr

#print axioms logical_forward
#print axioms logical_backward
end LRX.UpperAffineBuffer

namespace LRX.UpperNativeLift
open LRX.UpperAffineBuffer (contract)
variable {α : Type*} [DecidableEq α]

private theorem negative_residue (u n r : Int) (hr : 0<r) (hrn : r<n)
    (h : u%n=r) : (-u)%n=n-r := by
  have he := Int.emod_add_mul_ediv u n
  rw [h] at he
  have hx : -u=(n-r)+n*(-(u/n)-1) := by nlinarith
  rw [hx, Int.add_emod, Int.mul_emod_right, add_zero, Int.emod_emod]
  exact Int.emod_eq_of_lt (by omega) (by omega)

/-- Exact native XL diagram on every label, for arbitrary integer winding. -/
theorem macro_XL_logical (a b : α) (ps : List α) (H : Int) (z : α → Int)
    (hall : ∀ c, c∈a::b::ps) (hn : (a::b::ps).Nodup)
    (h : Represents (ps.length+2) H (a::b::ps) z) (c : α) :
    contract ((ps.length:Int)+1) (H+1) (exchange a b z c)=
      contract ((ps.length:Int)+1) H (z c)+(if c=a then 1 else 0) := by
  have hab : a≠b := by intro he; exact (List.nodup_cons.mp hn).1 (by simp [he])
  have hi := (residue_complete (a::b::ps) H z hall h).1
  have hp := native_residue (a::b::ps) H z h 1 (by simp)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.length_cons,
    Nat.cast_add, Nat.cast_one] at hp
  have hb := negative_residue (z b-H) ((ps.length:Int)+1+1) 1 (by omega) (by omega) hp
  have hx : -(z b-H)=H-z b := by ring
  rw [hx] at hb
  apply LRX.UpperAffineBuffer.logical_forward _ _ _ a b (by omega) hab
  · simpa using hi
  · convert hb using 1 <;> ring

/-- Exact native RX diagram, including the wrapped last passive label. -/
theorem macro_RX_logical (a b : α) (ps : List α) (H : Int) (z : α → Int)
    (hall : ∀ c, c∈((a::ps)++[b])) (hn : ((a::ps)++[b]).Nodup)
    (h : Represents (ps.length+2) H ((a::ps)++[b]) z) (c : α) :
    contract ((ps.length:Int)+1) (H-1) (exchange b a z c)=
      contract ((ps.length:Int)+1) H (z c)-(if c=a then 1 else 0) := by
  have hnp : (a::b::ps).Nodup := by
    have hperm : ((a::ps)++[b]).Perm (a::b::ps) := List.Perm.cons a List.perm_append_comm
    exact hperm.nodup_iff.mp hn
  have hab : a≠b := by intro he; exact (List.nodup_cons.mp hnp).1 (by simp [he])
  have hfull : Represents ((a::ps)++[b]).length H ((a::ps)++[b]) z := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hi := (residue_complete ((a::ps)++[b]) H z hall hfull).1
  obtain ⟨wa,hwa⟩ := h 0 (by simp)
  have hwa' : z a=H+((ps.length:Int)+2)*wa := by simpa using hwa
  have ha : (H-z a)%((ps.length:Int)+1+1)=0 := by
    rw [hwa']
    have hx : H-(H+((ps.length:Int)+2)*wa)=(-wa)*((ps.length:Int)+1+1) := by ring
    rw [hx, Int.mul_emod_left]
  have hp := native_residue ((a::ps)++[b]) H z hfull (ps.length+1) (by simp)
  have hget : ((a::ps)++[b])[ps.length+1]'(by simp)=b := by simp
  rw [hget] at hp
  simp only [List.length_append,List.length_cons,List.length_singleton,Nat.cast_add,Nat.cast_one] at hp
  have hb := negative_residue (z b-H) ((ps.length:Int)+1+1) ((ps.length:Int)+1) (by omega) (by omega) hp
  have hx : -(z b-H)=H-z b := by ring
  rw [hx] at hb
  apply LRX.UpperAffineBuffer.logical_backward _ _ _ a b (by omega) hab
  · simpa using hi
  · exact ha
  · convert hb using 1 <;> ring

#print axioms macro_XL_logical
#print axioms macro_RX_logical
end LRX.UpperNativeLift

