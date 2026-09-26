import UpperAffineBuffer

/-! Coordinate inverse for the double-site contraction. This does not construct
native states or prove recursive service. H is the physical cursor, z a token lift. -/
namespace LRX.UpperAffineBuffer

def contract (M H z : Int) : Int := z + (H-z)/(M+1)

/-- At a buffer position the contraction recovers its logical head-class lift. -/
theorem contract_buffer (M H y : Int) (hM : 0 < M)
    (hhead : (y-H)%M=0) : contract M H (buffer M H y) = y := by
  have he := Int.emod_add_mul_ediv (y-H) M
  rw [hhead] at he
  have hdiv : (H-buffer M H y)/(M+1) = -((y-H)/M) := by
    have hn : M+1 ≠ 0 := by omega
    have hx : H-buffer M H y = (-((y-H)/M))*(M+1) := by unfold buffer; ring
    rw [hx, Int.mul_ediv_cancel _ hn]
  unfold contract
  rw [hdiv]
  unfold buffer
  nlinarith

/-- Every passive logical lift has exactly its own contracted coordinate. -/
theorem contract_passive (M H y : Int) (hM : 0 < M) :
    contract M H (passive M H y) = y := by
  have he := Int.emod_add_mul_ediv (y-H) M
  have hr := Int.emod_nonneg (y-H) (by omega : M ≠ 0)
  have hu := Int.emod_lt_of_pos (y-H) hM
  have he' := Int.emod_add_mul_ediv (H-passive M H y) (M+1)
  have hr' := Int.emod_nonneg (H-passive M H y) (by omega : M+1 ≠ 0)
  have hu' := Int.emod_lt_of_pos (H-passive M H y) (by omega : 0<M+1)
  have hdiv : (H-passive M H y)/(M+1) = -((y-H)/M) - 1 := by
    by_contra hn
    have hc : (H-passive M H y)/(M+1) ≤ -((y-H)/M)-2 ∨
        -((y-H)/M) ≤ (H-passive M H y)/(M+1) := by omega
    unfold passive at he' hr' hu'
    rcases hc with hl | hh
    · unfold passive at hl
      nlinarith
    · unfold passive at hh
      nlinarith
  unfold contract
  rw [hdiv]
  unfold passive
  omega

/-- The zero remainder identifies the distinguished buffer member. -/
theorem buffer_contract (M H z : Int) (hM : 0 < M)
    (hz : (H-z)%(M+1)=0) : buffer M H (contract M H z) = z := by
  have he := Int.emod_add_mul_ediv (H-z) (M+1)
  rw [hz] at he
  have hx : contract M H z-H = (-((H-z)/(M+1)))*M := by
    unfold contract
    nlinarith
  unfold buffer
  rw [hx, Int.mul_ediv_cancel _ (by omega : M ≠ 0)]
  nlinarith

/-- Every other physical residue is the passive member at its logical site. -/
theorem passive_contract (M H z : Int) (hM : 0 < M)
    (hz : (H-z)%(M+1)≠0) : passive M H (contract M H z) = z := by
  have he := Int.emod_add_mul_ediv (H-z) (M+1)
  have hr := Int.emod_nonneg (H-z) (by omega : M+1≠0)
  have hu := Int.emod_lt_of_pos (H-z) (by omega : 0<M+1)
  have hpos : 1 ≤ (H-z)%(M+1) := by omega
  have he' := Int.emod_add_mul_ediv (contract M H z-H) M
  have hr' := Int.emod_nonneg (contract M H z-H) (by omega : M≠0)
  have hu' := Int.emod_lt_of_pos (contract M H z-H) hM
  have hdiv : (contract M H z-H)/M = -((H-z)/(M+1))-1 := by
    by_contra hn
    have hc : (contract M H z-H)/M ≤ -((H-z)/(M+1))-2 ∨
        -((H-z)/(M+1)) ≤ (contract M H z-H)/M := by omega
    unfold contract at he' hr' hu'
    rcases hc with hl | hh
    · unfold contract at hl
      nlinarith
    · unfold contract at hh
      nlinarith
  unfold passive
  rw [hdiv]
  unfold contract
  omega

#print axioms contract_buffer
#print axioms contract_passive
#print axioms buffer_contract
#print axioms passive_contract
end LRX.UpperAffineBuffer
