import UpperBufferContraction

/-! Tagged coordinate representation for U19 §4. This is a coordinate-level
relation, NOT yet a representation of an entire native permutation state. -/
namespace LRX.UpperAffineBuffer

def Represents (M H : Int) (isBuffer : Bool) (y z : Int) : Prop :=
  z = (if isBuffer then buffer M H y else passive M H y) ∧
  (isBuffer = true → (y-H)%M = 0)

theorem buffer_residue (M H y : Int) : (H-buffer M H y)%(M+1)=0 := by
  have hx : H-buffer M H y = (-((y-H)/M))*(M+1) := by unfold buffer; ring
  rw [hx, Int.mul_emod_left]

theorem passive_residue_ne (M H y : Int) (hM : 0<M) :
    (H-passive M H y)%(M+1) ≠ 0 := by
  intro hz
  have hb := buffer_contract M H (passive M H y) hM hz
  rw [contract_passive M H y hM] at hb
  have he := Int.emod_add_mul_ediv (y-H) M
  have hr := Int.emod_nonneg (y-H) (by omega : M≠0)
  unfold buffer passive at hb
  nlinarith

theorem contract_head (M H z : Int) (hM : 0<M)
    (hz : (H-z)%(M+1)=0) : (contract M H z-H)%M=0 := by
  have he := Int.emod_add_mul_ediv (H-z) (M+1)
  rw [hz] at he
  have hx : contract M H z-H = (-((H-z)/(M+1)))*M := by
    unfold contract
    nlinarith
  rw [hx, Int.mul_emod_left]

theorem represents_contract (M H y z : Int) (b : Bool) (hM : 0<M)
    (h : Represents M H b y z) : contract M H z = y := by
  cases b with
  | false => simpa [Represents] using h.1 ▸ contract_passive M H y hM
  | true =>
    have hz : z = buffer M H y := h.1
    rw [hz]
    exact contract_buffer M H y hM (h.2 rfl)

theorem represents_tag (M H y z : Int) (b : Bool) (hM : 0<M)
    (h : Represents M H b y z) :
    (b = true ↔ (H-z)%(M+1)=0) := by
  cases b with
  | false =>
    have hz : z = passive M H y := h.1
    rw [hz]
    simp [passive_residue_ne M H y hM]
  | true =>
    have hz : z = buffer M H y := h.1
    rw [hz]
    simp [buffer_residue]

/-- Every integer physical coordinate has a canonical tagged logical coordinate. -/
theorem represents_decode (M H z : Int) (hM : 0<M) :
    Represents M H (decide ((H-z)%(M+1)=0)) (contract M H z) z := by
  by_cases hz : (H-z)%(M+1)=0
  · simp only [hz, decide_true, Represents, Bool.true_eq, ↓reduceIte]
    exact ⟨(buffer_contract M H z hM hz).symm, fun _ => contract_head M H z hM hz⟩
  · simp only [hz, decide_false, Represents, Bool.false_eq_true, ↓reduceIte,
      false_implies, and_true]
    exact (passive_contract M H z hM hz).symm

/-- Tag and contracted coordinate cannot encode the same physical point twice. -/
theorem represents_unique (M H y y' z : Int) (b b' : Bool) (hM : 0<M)
    (h : Represents M H b y z) (h' : Represents M H b' y' z) :
    b=b' ∧ y=y' := by
  have hy := represents_contract M H y z b hM h
  have hy' := represents_contract M H y' z b' hM h'
  have hb := represents_tag M H y z b hM h
  have hb' := represents_tag M H y' z b' hM h'
  constructor
  · cases b <;> cases b' <;> simp_all
  · omega

/-- Moving the coordinate frame alone preserves representability after decoding.
No claim identifying this frame update with a native L/R word is made here. -/
theorem represents_reframe (M H z d : Int) (hM : 0<M) :
    Represents M (H+d) (decide ((H+d-z)%(M+1)=0)) (contract M (H+d) z) z :=
  represents_decode M (H+d) z hM

#print axioms buffer_residue
#print axioms passive_residue_ne
#print axioms contract_head
#print axioms represents_contract
#print axioms represents_tag
#print axioms represents_decode
#print axioms represents_unique
#print axioms represents_reframe
end LRX.UpperAffineBuffer
