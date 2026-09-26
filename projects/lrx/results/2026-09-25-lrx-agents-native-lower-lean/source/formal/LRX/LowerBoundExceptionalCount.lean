import LRX.LowerBoundCyclicContiguity
import LRX.LowerBoundPaidProjection

namespace LRX.LowerBoundExceptionalCount
open LRX.BlockExchange LRX.LowerBoundSwapCount LRX.LowerBoundPairParity
open LRX.Cycle11StructuralBridge LRX.LowerBoundPaidProjection
open scoped BigOperators
variable {α : Type*} [DecidableEq α] [Fintype α]

theorem head_event_sum (x y : α) (tail : List α) (hxy : x ≠ y) :
    (∑ a : α, ∑ b : α, if swapEvent a b .X (x::y::tail) then 1 else 0) = (2 : Nat) := by
  have he : ∀ a b : α,
      (if swapEvent a b .X (x::y::tail) then 1 else 0 : Nat) =
      (if a=x ∧ b=y then 1 else 0) + (if a=y ∧ b=x then 1 else 0) := by
    intro a b
    by_cases hax : a=x
    · subst a
      by_cases hby : b=y
      · subst b; simp [swapEvent, pairAtHead, hxy, Ne.symm hxy]
      · simp [swapEvent, pairAtHead, hxy, Ne.symm hxy, hby, Ne.symm hby]
    · by_cases hay : a=y
      · subst a
        by_cases hbx : b=x
        · subst b; simp [swapEvent, pairAtHead, hxy, Ne.symm hxy]
        · simp [swapEvent, pairAtHead, hxy, Ne.symm hxy, hbx, Ne.symm hbx]
      · simp [swapEvent, pairAtHead, hax, hay, Ne.symm hax, Ne.symm hay]
  simp_rw [he, Finset.sum_add_distrib]
  simp [ite_and]

/-- Each actual X contributes the two orientations of precisely one pair. -/
theorem actual_pair_count_sum (w : List Op) (s : List α)
    (hs : s.Nodup) (hlen : 2 ≤ s.length) :
    (∑ a : α, ∑ b : α, swapCount a b w s) = 2 * exchanges w := by
  induction w generalizing s with
  | nil => simp [swapCount, exchanges]
  | cons op w ih =>
    have hp := step_perm op s
    have ht := ih (step op s) (hp.nodup_iff.mpr hs) (by rw [hp.length_eq]; exact hlen)
    simp only [swapCount, Finset.sum_add_distrib]
    rw [ht]
    cases op with
    | L => simp [swapEvent, exchanges]
    | R => simp [swapEvent, exchanges]
    | X =>
      cases s with
      | nil => simp at hlen
      | cons x s => cases s with
        | nil => simp at hlen
        | cons y tail =>
          have hxy : x ≠ y := by
            have hh := List.nodup_cons.mp hs
            intro he; apply hh.1; simp [he]
          rw [head_event_sum x y tail hxy]
          simp only [exchanges]
          omega

/-- A complete set of actual pair encounters gives a lower X budget. -/
theorem complete_subset_exchange_bound (S : Finset α) (w : List Op) (s : List α)
    (hs : s.Nodup) (hlen : 2 ≤ s.length)
    (hc : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → swapCount a b w s = 1) :
    S.card * (S.card - 1) ≤ 2 * exchanges w := by
  have hpoint : ∀ a b : α,
      (if a∈S ∧ b∈S ∧ a≠b then 1 else 0 : Nat) ≤ swapCount a b w s := by
    intro a b
    split_ifs with h
    · rw [hc a h.1 b h.2.1 h.2.2]
    · exact Nat.zero_le _
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun b _ => hpoint a b))
  have hcalc : (∑ a : α, ∑ b : α,
      if a∈S ∧ b∈S ∧ a≠b then 1 else 0 : Nat) = S.card * (S.card-1) := by
    have hrow : ∀ a : α, (∑ b : α, if a∈S ∧ b∈S ∧ a≠b then 1 else 0 : Nat) =
        if a∈S then S.card-1 else 0 := by
      intro a
      by_cases ha : a∈S
      · have he : ∀ b : α, (a∈S ∧ b∈S ∧ a≠b) ↔ b∈S.erase a := by
          intro b; simp [Finset.mem_erase, ha, ne_comm, and_comm]
        simp_rw [he]
        rw [if_pos ha]
        rw [← Finset.sum_filter]
        simp only [Finset.filter_mem_eq_inter, Finset.univ_inter,
          Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem ha]
      · simp [ha]
    simp_rw [hrow]
    simp
  rw [hcalc, actual_pair_count_sum w s hs hlen] at hsum
  exact hsum

#print axioms actual_pair_count_sum
#print axioms complete_subset_exchange_bound
end LRX.LowerBoundExceptionalCount
