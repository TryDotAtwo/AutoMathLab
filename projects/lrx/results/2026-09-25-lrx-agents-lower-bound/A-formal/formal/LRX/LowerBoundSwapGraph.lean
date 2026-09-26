import Mathlib.Tactic.Linarith

/-! Algebraic part of the reflection swap-graph reduction.
The hypotheses express parity of actual label-pair swaps. Establishing those
hypotheses from concrete LRX words, and no repeated pairs in a shortest word,
are separate obligations, not assumed proved by this module. -/
namespace LRX.LowerBoundSwapGraph
variable {α : Type*}

def color [DecidableEq α] (e : α → α → Bool) (z a : α) : Bool :=
  if a = z then false else !(e z a)

/-- Every graph with odd edge parity on every triple is two disjoint cliques.
Diagonal values are irrelevant: the conclusion is only for distinct vertices. -/
theorem two_cliques [DecidableEq α] (e : α → α → Bool) (z : α)
    (sym : ∀ a b, e a b = e b a)
    (tri : ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
      ((e a b ^^ e a c) ^^ e b c) = true)
    (a b : α) (hab : a ≠ b) :
    e a b = (color e z a == color e z b) := by
  by_cases ha : a = z
  · subst a
    have hb : b ≠ z := Ne.symm hab
    cases he : e z b <;> simp [color, hb, he]
  · by_cases hb : b = z
    · subst b
      rw [sym a z]
      cases he : e z a <;> simp [color, ha, he]
    · have ht := tri z a b (Ne.symm ha) (Ne.symm hb) hab
      simp only [color, ite_eq_right ha, ite_eq_right hb]
      cases hza : e z a <;> cases hzb : e z b <;> cases habv : e a b <;>
        simp_all

/-- Exact polynomial resource separating swap count from cursor cost.
No cursor lower bound is established by this identity. -/
theorem joint_budget_identity (a b m N : Int)
    (hm : 2*m = a*(a-1)+b*(b-1))
    (hN : 2*N = (a+b)*(a+b-1)) :
    2*(N-m) = 2*a*b := by nlinarith

/-- Under the exact swap count, the missing joint budget is precisely r ≥ a*b. -/
theorem remaining_budget_iff (a b m N r : Int)
    (hm : 2*m = a*(a-1)+b*(b-1))
    (hN : 2*N = (a+b)*(a+b-1)) :
    N ≤ m+r ↔ a*b ≤ r := by
  have h := joint_budget_identity a b m N hm hN
  constructor <;> intro hr <;> nlinarith

/-- The proved weak route bound closes all sufficiently unbalanced sizes.
The route bound remains an explicit hypothesis in this algebraic statement. -/
theorem far_from_balanced (a b m N r : Int)
    (hm : 2*m = a*(a-1)+b*(b-1))
    (hN : 2*N = (a+b)*(a+b-1))
    (hr : m+1 ≤ r) (hgap : a+b-2 ≤ (a-b)^2) :
    N ≤ m+r := by nlinarith

#print axioms two_cliques
#print axioms joint_budget_identity
#print axioms remaining_budget_iff
#print axioms far_from_balanced
end LRX.LowerBoundSwapGraph
