import Navigation
set_option Elab.async false

namespace Astra3Navigation

theorem shift_coord (n s a : Nat) (hs : s < n) (ha : a < n) :
    (s+a)%n = if s+a < n then s+a else s+a-n := by
  split
  · next h => exact Nat.mod_eq_of_lt h
  · next h =>
    have heq : s+a = n+(s+a-n) := by omega
    have hr : s+a-n < n := by omega
    rw [heq, Nat.add_mod]
    simp only [Nat.mod_self, Nat.zero_add, Nat.mod_mod]
    rw [Nat.mod_eq_of_lt hr]
    omega

/- Coordinate change only: both positions rotate together. No operation
   is erased from a word and no cost is declared free. -/
theorem distance_shift (n s a b : Nat) (hs : s < n) (ha : a < n) (hb : b < n) :
    distance n ((s+a)%n) ((s+b)%n) = distance n a b := by
  rw [shift_coord n s a hs ha, shift_coord n s b hs hb]
  split <;> split <;>
    simp only [distance, linearDistance] <;> split <;> split <;> omega

/- The first approach goes to the selected cut, NOT the first endpoint
   of the second approach. Only equality of the complete site multisets
   permits replacement of its SUM; there is no pointwise substitution. -/
theorem three_site_navigation (n : Nat) (sites : List (Nat × Nat × Nat))
    (bounds : ∀ p ∈ sites, p.2.1 < n ∧ p.2.2 < n)
    (cut_endpoint : (sites.map Prod.fst).Perm (sites.map (fun p => p.2.1)))
    (endpoints : (sites.map (fun p => p.2.1)).Perm (sites.map (fun p => p.2.2))) :
    4*((sites.map (fun p => distance n 0 p.1)).sum +
       (sites.map (fun p => distance n p.2.1 p.2.2)).sum) ≤ 3*n*sites.length := by
  have balanced := perm_weight_sum (distance n 0) cut_endpoint
  simp only [List.map_map, Function.comp_def] at balanced
  have hpairs : ∀ p ∈ sites.map Prod.snd, p.1 < n ∧ p.2 < n := by
    intro p hp
    obtain ⟨q, hq, heq⟩ := List.mem_map.mp hp
    subst p
    exact bounds q hq
  have hperm : ((sites.map Prod.snd).map Prod.fst).Perm
      ((sites.map Prod.snd).map Prod.snd) := by
    simpa only [List.map_map, Function.comp_def] using endpoints
  have h := navigation_average n (sites.map Prod.snd) hpairs hperm
  simp only [List.map_map, Function.comp_def, List.length_map] at h
  rw [balanced]
  exact h

def siteShift (k : Nat) (sites : List Nat) : List Nat :=
  sites.drop k ++ sites.take k

theorem siteShift_perm (k : Nat) (sites : List Nat) :
    (siteShift k sites).Perm sites := by
  have h : (sites.drop k ++ sites.take k).Perm (sites.take k ++ sites.drop k) :=
    List.perm_append_comm
  simpa only [siteShift, List.take_append_drop] using h

/- Explicit cyclic endpoint enumeration. The cut list is sites itself;
   its two endpoint lists are shifted by fixed occupied-token offsets.
   Unlike three_site_navigation, this theorem assumes no Perm premises. -/
theorem cyclic_navigation (n k l : Nat) (sites : List Nat)
    (bounded : ∀ s ∈ sites, s < n) :
    4*((sites.map (distance n 0)).sum +
      (((siteShift k sites).zip (siteShift l sites)).map
        (fun p => distance n p.1 p.2)).sum) ≤ 3*n*sites.length := by
  have pk := siteShift_perm k sites
  have pl := siteShift_perm l sites
  have hk := pk.length_eq
  have hl := pl.length_eq
  have fst : (((siteShift k sites).zip (siteShift l sites)).map Prod.fst) =
      siteShift k sites := List.map_fst_zip (by omega)
  have snd : (((siteShift k sites).zip (siteShift l sites)).map Prod.snd) =
      siteShift l sites := List.map_snd_zip (by omega)
  have hlen : ((siteShift k sites).zip (siteShift l sites)).length = sites.length := by
    have h := congrArg List.length fst
    simpa only [List.length_map, hk] using h
  have bounds : ∀ p ∈ (siteShift k sites).zip (siteShift l sites),
      p.1 < n ∧ p.2 < n := by
    intro p hp
    have h := List.of_mem_zip hp
    constructor
    · exact bounded p.1 (pk.mem_iff.mp h.1)
    · exact bounded p.2 (pl.mem_iff.mp h.2)
  have perm : ((((siteShift k sites).zip (siteShift l sites)).map Prod.fst)).Perm
      ((((siteShift k sites).zip (siteShift l sites)).map Prod.snd)) := by
    rw [fst, snd]
    exact pk.trans pl.symm
  have h := navigation_average n ((siteShift k sites).zip (siteShift l sites)) bounds perm
  have sums := perm_weight_sum (distance n 0) pk
  have firstSum : ((((siteShift k sites).zip (siteShift l sites)).map
      (fun p => distance n 0 p.1)).sum) = (sites.map (distance n 0)).sum := by
    have heq := congrArg (fun xs => (xs.map (distance n 0)).sum) fst
    simp only [List.map_map, Function.comp_def] at heq
    exact heq.trans sums
  rw [firstSum, hlen] at h
  exact h

end Astra3Navigation

#print axioms Astra3Navigation.shift_coord
#print axioms Astra3Navigation.distance_shift
#print axioms Astra3Navigation.three_site_navigation
#print axioms Astra3Navigation.siteShift_perm
#print axioms Astra3Navigation.cyclic_navigation
