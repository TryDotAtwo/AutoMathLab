import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Tauto

/-! Mathematical square-root bounds used by the U19 scalar pruning.
These specifications do not formalize C++ machine arithmetic or its binary-search loops. -/
namespace LRX.UpperScalarSqrt

def floorSqrt (z : Int) : Int := if z < 0 then -1 else Int.sqrt z
def ceilSqrt (z : Int) : Int := if z ≤ 0 then 0 else Int.sqrt (z-1)+1

theorem le_intSqrt_iff (x z : Int) (hx : 0 ≤ x) (hz : 0 ≤ z) :
    x ≤ Int.sqrt z ↔ x^2 ≤ z := by
  lift x to Nat using hx
  lift z to Nat using hz
  rw [Int.sqrt_natCast]
  exact_mod_cast (Nat.le_sqrt' : x ≤ Nat.sqrt z ↔ x^2 ≤ z)

theorem le_floorSqrt_iff (x z : Int) (hx : 0 ≤ x) :
    x ≤ floorSqrt z ↔ x^2 ≤ z := by
  unfold floorSqrt
  split_ifs with hz
  · have hs := sq_nonneg x
    constructor <;> intro h <;> omega
  · exact le_intSqrt_iff x z hx (by omega)

theorem ceilSqrt_nonneg (z : Int) : 0 ≤ ceilSqrt z := by
  unfold ceilSqrt
  split_ifs
  · omega
  · have := Int.sqrt_nonneg (z-1)
    omega

theorem ceilSqrt_le_iff (x z : Int) (hx : 0 ≤ x) :
    ceilSqrt z ≤ x ↔ z ≤ x^2 := by
  unfold ceilSqrt
  split_ifs with hz
  · have hs := sq_nonneg x
    constructor <;> intro h <;> omega
  · have h := le_intSqrt_iff x (z-1) hx (by omega)
    omega

theorem branch_zero_iff (x cap z u : Int) (hx : 0 ≤ x) :
    (ceilSqrt z ≤ x ∧ x ≤ min cap u) ↔
      (x ≤ cap ∧ x ≤ u ∧ z ≤ x^2) := by
  rw [ceilSqrt_le_iff x z hx, le_min_iff]
  tauto

theorem branch_one_iff (x cap z u : Int) :
    (cap + ceilSqrt (z-cap^2) ≤ x ∧ x ≤ u) ↔
      (cap ≤ x ∧ x ≤ u ∧ z ≤ cap^2+(x-cap)^2) := by
  constructor
  · rintro ⟨hl, hu⟩
    have hn := ceilSqrt_nonneg (z-cap^2)
    have hx : 0 ≤ x-cap := by omega
    have hs := (ceilSqrt_le_iff (x-cap) (z-cap^2) hx).1 (by omega)
    exact ⟨by omega, hu, by omega⟩
  · rintro ⟨hc, hu, hs⟩
    have hx : 0 ≤ x-cap := by omega
    have hl := (ceilSqrt_le_iff (x-cap) (z-cap^2) hx).2 (by omega)
    exact ⟨by omega, hu⟩

/-- The two C++ branches cover exactly the piecewise square envelope.
At x=cap they overlap harmlessly, which is why the output is deduplicated. -/
theorem branch_union_iff (x cap z u : Int) (hx : 0 ≤ x) :
    ((ceilSqrt z ≤ x ∧ x ≤ min cap u) ∨
     (cap + ceilSqrt (z-cap^2) ≤ x ∧ x ≤ u)) ↔
      (x ≤ u ∧ z ≤ if x ≤ cap then x^2 else cap^2+(x-cap)^2) := by
  rw [branch_zero_iff x cap z u hx, branch_one_iff]
  by_cases hc : x ≤ cap
  · rw [if_pos hc]
    constructor
    · rintro (h | h)
      · exact ⟨h.2.1, h.2.2⟩
      · have he : x = cap := by omega
        subst x
        simpa using h.2
    · rintro ⟨hu, hs⟩
      exact Or.inl ⟨hc, hu, hs⟩
  · rw [if_neg hc]
    constructor
    · rintro (h | h)
      · omega
      · exact h.2
    · rintro ⟨hu, hs⟩
      exact Or.inr ⟨by omega, hu, hs⟩

#print axioms le_intSqrt_iff
#print axioms le_floorSqrt_iff
#print axioms ceilSqrt_nonneg
#print axioms ceilSqrt_le_iff
#print axioms branch_zero_iff
#print axioms branch_one_iff
#print axioms branch_union_iff
end LRX.UpperScalarSqrt
