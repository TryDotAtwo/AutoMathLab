import Mathlib.Tactic
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace LRX.UpperExceptionalTours

def cyc (n a b : Nat) : Nat := min (a-b+(b-a)) (n-(a-b+(b-a)))
def tour (n s t a b c : Nat) : Nat :=
  cyc n s a + cyc n a b + cyc n b c + cyc n c t

abbrev HasTour (n h s t : Nat) : Prop :=
  tour n s t 0 2 h ≤ n ∨ tour n s t 0 h 2 ≤ n ∨
  tour n s t 2 0 h ≤ n ∨ tour n s t 2 h 0 ≤ n ∨
  tour n s t h 0 2 ≤ n ∨ tour n s t h 2 0 ≤ n

-- Kernel reduction of finite propositions, not native_decide or an external C++ axiom.
theorem tours16 : ∀ h s t : Fin 16, HasTour 16 h.val s.val t.val := by decide
theorem tours20 : ∀ h s t : Fin 20, HasTour 20 h.val s.val t.val := by decide

#print axioms tours16
#print axioms tours20
end LRX.UpperExceptionalTours
