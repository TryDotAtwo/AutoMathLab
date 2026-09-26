import LRX.LowerBoundCyclicContiguity
import LRX.LowerBoundPaidProjection
import Mathlib.Tactic.NormNum

/-! B, LB-L0: exceptional color classes in the original paid list semantics.
The counting assumptions below refer to actual pair exchanges, never to a
physical trace or to the desired length lower bound. -/
namespace LRX.LowerBoundExceptional
open LRX.BlockExchange LRX.LowerBoundNoRepeat LRX.LowerBoundSwapCount
open LRX.LowerBoundPairParity LRX.Cycle11StructuralBridge
open LRX.LowerBoundFoldedTransport LRX.LowerBoundPaidProjection
open scoped BigOperators
variable {α : Type*} [DecidableEq α]

theorem swap_involutive (s : List α) : swap (swap s) = s := by
  cases s with
  | nil => rfl
  | cons x s => cases s <;> rfl

theorem shortest_not_xx (w : List Op) (s : List α) :
    ¬ Shortest (.X :: .X :: w) s := by
  intro h
  have he : run w s = run (.X :: .X :: w) s := by
    simp only [run, step, swap_involutive]
  have := h w he
  simp only [List.length_cons] at this
  omega

/-- Every two consecutive X letters in a shortest word are separated by
at least one paid rotation. No restriction on the endpoints is needed. -/
def initialX : List Op → Nat
  | .X :: _ => 1
  | _ => 0

theorem shortest_exchange_budget_aux (w : List Op) (s : List α)
    (h : Shortest w s) : exchanges w ≤ rotations w + initialX w := by
  induction w generalizing s with
  | nil => simp [exchanges, rotations, initialX]
  | cons op w ih =>
    have ht := shortest_tail op w s h
    have hb := ih (step op s) ht
    cases op with
    | L =>
      have : initialX w ≤ 1 := by cases w with
        | nil => decide
        | cons op w => cases op <;> simp [initialX]
      simp only [exchanges, rotations, price, initialX]; omega
    | R =>
      have : initialX w ≤ 1 := by cases w with
        | nil => decide
        | cons op w => cases op <;> simp [initialX]
      simp only [exchanges, rotations, price, initialX]; omega
    | X =>
      cases w with
      | nil => simp [exchanges, rotations, price, initialX]
      | cons op w =>
        cases op with
        | X => exact False.elim (shortest_not_xx w s h)
        | L =>
          simp only [exchanges, rotations, price, initialX] at hb ⊢
          omega
        | R =>
          simp only [exchanges, rotations, price, initialX] at hb ⊢
          omega

theorem shortest_exchange_budget (w : List Op) (s : List α)
    (h : Shortest w s) : exchanges w ≤ rotations w + 1 := by
  have hh := shortest_exchange_budget_aux w s h
  have : initialX w ≤ 1 := by cases w with
    | nil => decide
    | cons op w => cases op <;> simp [initialX]
  omega

end LRX.LowerBoundExceptional
