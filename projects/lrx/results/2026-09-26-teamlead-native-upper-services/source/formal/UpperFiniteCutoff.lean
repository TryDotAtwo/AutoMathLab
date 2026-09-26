import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-! Uskov19 §11.3 equations (44),(47),(48), scalar implication ONLY.
The hypotheses still need to be derived from an arbitrary LRX counterexample. -/
namespace LRX.UpperFiniteCutoff

def Branch (t m : Int) : Prop :=
  m ≤ 42*t+23 ∨ 8*(t-2)*(m-1) ≤ (28*t-4)^2+6*t-3

theorem component_cutoff (t m : Int) (ht : 3≤t)
    (hlo : t^3-3*t^2+3*t+1 ≤ m) (hb : Branch t m) : t≤12 := by
  by_contra hn
  have hz : 0≤t-13 := by omega
  let z := t-13
  have hz0 : 0≤z := hz
  have hz2 : 0≤z^2 := sq_nonneg z
  have hz3 : 0≤z^3 := pow_nonneg hz0 3
  have hz4 : 0≤z^4 := pow_nonneg hz0 4
  have htval : t=z+13 := by dsimp [z]; ring
  rcases hb with hsmall|hlarge
  · have hpoly : 0 < t^3-3*t^2-39*t-22 := by
      rw [htval]
      nlinarith
    linarith
  · have hmul := mul_le_mul_of_nonneg_left hlo (by omega : 0≤8*(t-2))
    have hpoly : 0 < 8*t^4-40*t^3-712*t^2+170*t-13 := by
      rw [htval]
      nlinarith
    nlinarith [hmul]

theorem half_size_cutoff (t m : Int) (ht : 2≤t)
    (htwo : t=2 → m≤732)
    (hlo : 3≤t → t^3-3*t^2+3*t+1 ≤ m)
    (hb : Branch t m) : m≤1379 := by
  by_cases h2 : t=2
  · have := htwo h2; omega
  · have ht3 : 3≤t := by omega
    have ht12 := component_cutoff t m ht3 (hlo ht3) hb
    rcases hb with hsmall|hlarge
    · omega
    · interval_cases t <;> norm_num at hlarge ⊢ <;> linarith

theorem size_cutoff (n t m : Int) (ht : 2≤t)
    (htwo : t=2 → m≤732)
    (hlo : 3≤t → t^3-3*t^2+3*t+1 ≤ m)
    (hb : Branch t m) (hn : n≤2*m+1) : n≤2759 := by
  have := half_size_cutoff t m ht htwo hlo hb
  omega

#print axioms component_cutoff
#print axioms half_size_cutoff
#print axioms size_cutoff
end LRX.UpperFiniteCutoff
