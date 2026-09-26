import Mathlib

/-! Balanced phase-compatible lifts selected by quadratic energy.
This file does not assume the desired majorization or a minimizer.
It does not claim minimality of affine inversion count or a paid LRX route. -/
namespace LRX.UpperLiftSelection
open Finset

variable {n : ℕ}
def Balanced (d : Fin n → ℤ) : Prop := ∑ i, d i = 0
def Compatible (p : Equiv.Perm (Fin n)) (c : ℤ) (d : Fin n → ℤ) : Prop :=
  ∃ w : Fin n → ℤ, ∀ i, (i.val : ℤ) + d i = (p i).val + c + (n : ℤ) * w i
def Energy (d : Fin n → ℤ) : ℤ := ∑ i, (d i)^2

theorem energy_nonneg (d : Fin n → ℤ) : 0 ≤ Energy d := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (d i))

theorem initial_lift (p : Equiv.Perm (Fin n)) :
    ∃ d, Balanced d ∧ Compatible p 0 d := by
  refine ⟨fun i => ((p i).val : ℤ) - i.val, ?_, ?_⟩
  · unfold Balanced
    rw [Finset.sum_sub_distrib]
    have h := Equiv.sum_comp p (fun i : Fin n => (i.val : ℤ))
    exact sub_eq_zero.mpr h
  · refine ⟨fun _ => 0, ?_⟩
    intro i
    simp

theorem exists_energy_minimizer (p : Equiv.Perm (Fin n)) :
    ∃ c d, Balanced d ∧ Compatible p c d ∧
      ∀ c' d', Balanced d' → Compatible p c' d' → Energy d ≤ Energy d' := by
  classical
  obtain ⟨d₀,hb,hc⟩ := initial_lift p
  have hex : ∃ m : ℕ, ∃ c d, Balanced d ∧ Compatible p c d ∧
      (Energy d).toNat = m := ⟨(Energy d₀).toNat, 0, d₀, hb, hc, rfl⟩
  obtain ⟨c,d,hb,hc,he⟩ := Nat.find_spec hex
  refine ⟨c,d,hb,hc,?_⟩
  intro c' d' hb' hc'
  have hmin := Nat.find_min' hex (show ∃ c d, Balanced d ∧ Compatible p c d ∧
      (Energy d).toNat = (Energy d').toNat from ⟨c',d',hb',hc',rfl⟩)
  rw [← he] at hmin
  have hn₁ := energy_nonneg d
  have hn₂ := energy_nonneg d'
  omega

def Shift (d : Fin n → ℤ) (s : Finset (Fin n)) (i : Fin n) : ℤ :=
  d i + s.card - if i ∈ s then (n : ℤ) else 0

theorem sum_indicator (s : Finset (Fin n)) (g : Fin n → ℤ) :
    (∑ i, if i ∈ s then g i else 0) = ∑ i ∈ s, g i := by
  simp

theorem shift_balanced (d : Fin n → ℤ) (s : Finset (Fin n))
    (hb : Balanced d) : Balanced (Shift d s) := by
  unfold Balanced Shift at *
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [sum_indicator]
  simp [hb]
  ring

theorem shift_compatible (p : Equiv.Perm (Fin n)) (c : ℤ)
    (d : Fin n → ℤ) (s : Finset (Fin n)) (hc : Compatible p c d) :
    Compatible p (c+s.card) (Shift d s) := by
  obtain ⟨w,hw⟩ := hc
  refine ⟨fun i => w i - if i ∈ s then 1 else 0, ?_⟩
  intro i
  unfold Shift
  by_cases hi : i ∈ s <;> simp only [hi, ite_true, ite_false]
  · nlinarith [hw i]
  · nlinarith [hw i]

theorem shift_energy (d : Fin n → ℤ) (s : Finset (Fin n)) (hb : Balanced d) :
    Energy (Shift d s) = Energy d + (n : ℤ) *
      ((s.card : ℤ) * ((n : ℤ)-s.card) - 2 * ∑ i ∈ s, d i) := by
  have point (i : Fin n) :
      (Shift d s i)^2 = (d i)^2 + 2*(s.card : ℤ)*d i + (s.card : ℤ)^2 +
        (if i ∈ s then (n : ℤ)^2 - 2*(n : ℤ)*d i - 2*(n : ℤ)*s.card else 0) := by
    unfold Shift
    split_ifs <;> ring
  unfold Energy
  simp_rw [point]
  simp only [Finset.sum_add_distrib]
  rw [sum_indicator]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [show (∑ i, d i)=0 from hb]
  ring

theorem minimizer_subset_bound (p : Equiv.Perm (Fin n)) (hn : 0 < n)
    (c : ℤ) (d : Fin n → ℤ) (hb : Balanced d) (hc : Compatible p c d)
    (hm : ∀ c' d', Balanced d' → Compatible p c' d' → Energy d ≤ Energy d')
    (s : Finset (Fin n)) :
    2 * (∑ i ∈ s, d i) ≤ (s.card : ℤ) * ((n : ℤ)-s.card) := by
  have hmin := hm (c+s.card) (Shift d s) (shift_balanced d s hb)
    (shift_compatible p c d s hc)
  rw [shift_energy d s hb] at hmin
  have hpos : (0 : ℤ) < n := by exact_mod_cast hn
  have hprod : 0 ≤ (n : ℤ)*((s.card : ℤ)*((n : ℤ)-s.card)-2*(∑ i ∈ s,d i)) := by
    linarith
  have hnonneg := (mul_nonneg_iff_of_pos_left hpos).mp hprod
  linarith

theorem subset_bounds_short (d : Fin n → ℤ) (hn : 0 < n) (hb : Balanced d)
    (hs : ∀ s : Finset (Fin n), 2 * (∑ i ∈ s, d i) ≤
      (s.card : ℤ) * ((n : ℤ)-s.card)) (i : Fin n) :
    2 * |d i| ≤ (n : ℤ)-1 := by
  have hu := hs {i}
  simp only [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, one_mul] at hu
  have hl := hs (Finset.univ.erase i)
  have hi : i ∈ (Finset.univ : Finset (Fin n)) := by simp
  have he := Finset.sum_erase_add (s := Finset.univ) d hi
  have heq : (∑ j ∈ Finset.univ.erase i, d j) = -d i := by
    change (∑ j ∈ Finset.univ.erase i, d j) + d i = ∑ j, d j at he
    rw [show (∑ j,d j)=0 from hb] at he
    omega
  have hcard : ((Finset.univ.erase i).card : ℤ) = (n : ℤ)-1 := by
    rw [Finset.card_erase_of_mem hi]
    simp only [Finset.card_univ, Fintype.card_fin]
    exact Nat.cast_sub (by omega)
  rw [heq,hcard] at hl
  have hl' : -(n : ℤ)+1 ≤ 2*d i := by nlinarith
  rcases le_total 0 (d i) with hp|hm
  · rw [abs_of_nonneg hp]; exact hu
  · rw [abs_of_nonpos hm]; omega

theorem exists_majorized_short_lift (p : Equiv.Perm (Fin n)) (hn : 0 < n) :
    ∃ c d, Balanced d ∧ Compatible p c d ∧
      (∀ s : Finset (Fin n), 2 * (∑ i ∈ s, d i) ≤
        (s.card : ℤ) * ((n : ℤ)-s.card)) ∧
      (∀ i, 2*|d i| ≤ (n : ℤ)-1) := by
  obtain ⟨c,d,hb,hc,hm⟩ := exists_energy_minimizer p
  have hs := minimizer_subset_bound p hn c d hb hc hm
  exact ⟨c,d,hb,hc,hs,subset_bounds_short d hn hb hs⟩

#print axioms initial_lift
#print axioms exists_energy_minimizer
#print axioms shift_energy
#print axioms exists_majorized_short_lift
end LRX.UpperLiftSelection
