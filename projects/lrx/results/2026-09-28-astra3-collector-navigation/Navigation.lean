import Init
set_option Elab.async false

namespace Astra3Navigation

/- Shortest circle distance using representatives in [0,n). -/
def linearDistance (a b : Nat) : Nat := if a ≤ b then b-a else a-b
def distance (n a b : Nat) : Nat :=
  min (linearDistance a b) (n-linearDistance a b)

theorem half_circle (n a b : Nat) (ha : a < n) (_hb : b < n) :
    2 * distance n a b ≤ n := by
  unfold distance linearDistance
  split <;> omega

theorem perimeter (n x y : Nat) (hx : x < n) (hy : y < n) :
    distance n 0 x + distance n 0 y + distance n x y ≤ n := by
  unfold distance linearDistance
  simp only [Nat.zero_le, if_true, Nat.sub_zero]
  split <;> omega

/- Pointwise bound used before summing over the occupied-site permutation.
   All distances are actual paid rotations, not free phase changes. -/
theorem navigation_pair (n x y : Nat) (hx : x < n) (hy : y < n) :
    2 * (distance n 0 x + distance n 0 y + 2 * distance n x y) ≤ 3*n := by
  have h := perimeter n x y hx hy
  have h' := half_circle n x y hx hy
  omega

/- Connect to the modular distance in the original source, rather than
   relying only on a newly introduced distance with a convenient name. -/
theorem distance_mod (n a b : Nat) (ha : a < n) (hb : b < n) :
    distance n a b = min ((a+n-b)%n) ((b+n-a)%n) := by
  by_cases hab : a = b
  · subst b
    have h : a+n-a = n := by omega
    simp [distance, linearDistance, h]
  · by_cases hle : a ≤ b
    · have hsmall : a+n-b < n := by omega
      have hdecomp : b+n-a = n+(b-a) := by omega
      rw [Nat.mod_eq_of_lt hsmall, hdecomp, Nat.add_mod]
      simp only [Nat.mod_self, Nat.zero_add, Nat.mod_mod]
      rw [Nat.mod_eq_of_lt (show b-a<n by omega)]
      simp only [distance, linearDistance, if_pos hle]
      have heq : a+n-b = n-(b-a) := by omega
      rw [heq, Nat.min_comm]
    · have hsmall : b+n-a < n := by omega
      have hdecomp : a+n-b = n+(a-b) := by omega
      rw [Nat.mod_eq_of_lt hsmall, hdecomp, Nat.add_mod]
      simp only [Nat.mod_self, Nat.zero_add, Nat.mod_mod]
      rw [Nat.mod_eq_of_lt (show a-b<n by omega)]
      simp only [distance, linearDistance, if_neg hle]
      congr 1
      omega

theorem perm_weight_sum (f : Nat → Nat) {xs ys : List Nat} (h : xs.Perm ys) :
    (xs.map f).sum = (ys.map f).sum := by
  induction h with
  | nil => rfl
  | cons a h ih => simp [ih]
  | swap a b tail => simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem navigation_total (n : Nat) (pairs : List (Nat × Nat))
    (bounds : ∀ p ∈ pairs, p.1 < n ∧ p.2 < n) :
    2*(pairs.map (fun p => distance n 0 p.1)).sum +
    2*(pairs.map (fun p => distance n 0 p.2)).sum +
    4*(pairs.map (fun p => distance n p.1 p.2)).sum ≤ 3*n*pairs.length := by
  induction pairs with
  | nil => simp
  | cons p pairs ih =>
    have hp := bounds p (by simp)
    have htail : ∀ q ∈ pairs, q.1 < n ∧ q.2 < n := by
      intro q hq
      exact bounds q (by simp [hq])
    have hsum := ih htail
    have hpoint := navigation_pair n p.1 p.2 hp.1 hp.2
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add,
      Nat.mul_one]
    omega

/- A shift of the occupied-site indices is a permutation; no disjoint
   pairing, even m, or independently chosen minimizers are assumed. -/
theorem navigation_average (n : Nat) (pairs : List (Nat × Nat))
    (bounds : ∀ p ∈ pairs, p.1 < n ∧ p.2 < n)
    (same_sites : (pairs.map Prod.fst).Perm (pairs.map Prod.snd)) :
    4*((pairs.map (fun p => distance n 0 p.1)).sum +
       (pairs.map (fun p => distance n p.1 p.2)).sum) ≤ 3*n*pairs.length := by
  have hbalance := perm_weight_sum (distance n 0) same_sites
  simp only [List.map_map, Function.comp_def] at hbalance
  have htotal := navigation_total n pairs bounds
  omega

end Astra3Navigation

#print axioms Astra3Navigation.navigation_pair
#print axioms Astra3Navigation.distance_mod
#print axioms Astra3Navigation.navigation_average
