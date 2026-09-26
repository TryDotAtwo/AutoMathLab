import Mathlib.Tactic.Linarith

/-! Algebraic impossibility of a head-label plus cursor-position potential.
The translation from actual local L/R/X inequalities is documented separately;
no assertion of a universal route lower bound is made here. -/
namespace LRX.LowerBoundPotentialBarrier

theorem telescope (f : Nat → Rat) (weight : Rat) (k : Nat)
    (h : ∀ i, i<k → weight≤f i-f (i+1)) :
    (k : Rat)*weight≤f 0-f k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (Nat.lt_succ_self k)
    have hh := ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self k)))
    push_cast
    linarith

/-- k is the difference between the smallest and largest label ranks.
All local ascending-X constraints and both directed rotation constraints
are displayed. -/
theorem head_weight_bound (f : Nat → Rat) (weight p q : Rat) (k : Nat)
    (hX : ∀ i, i<k → weight≤f i-f (i+1))
    (hL : f 0-f k+q-p≤1) (hR : f 0-f k+p-q≤1) :
    (k : Rat)*weight≤1 := by
  have hh := telescope f weight k hX
  linarith

theorem no_unit_head_potential (f : Nat → Rat) (p q : Rat) (k : Nat)
    (hk : 2≤k) (hX : ∀ i, i<k → (1 : Rat)≤f i-f (i+1))
    (hL : f 0-f k+q-p≤1) (hR : f 0-f k+p-q≤1) : False := by
  have hh := head_weight_bound f 1 p q k hX hL hR
  have hk' : (2 : Rat)≤k := by exact_mod_cast hk
  linarith

/-- Three X inequalities and four actual three-label rotation inequalities.
`d` is the position correction across one internal cursor step. -/
theorem two_head_step_bound (f01 f10 f02 f20 f12 f21 weight d : Rat)
    (hx01 : weight≤f01-f10) (hx02 : weight≤f02-f20)
    (hx12 : weight≤f12-f21)
    (hl201 : f01-f20+d≤1) (hl102 : f02-f10+d≤1)
    (hr021 : f02-f21-d≤1) (hr120 : f12-f20-d≤1) :
    weight≤1 ∧ weight-1≤d ∧ d≤1-weight := by
  constructor
  · linarith
  constructor <;> linarith

theorem two_head_unit_flat (f01 f10 f02 f20 f12 f21 d : Rat)
    (hx01 : 1≤f01-f10) (hx02 : 1≤f02-f20) (hx12 : 1≤f12-f21)
    (hl201 : f01-f20+d≤1) (hl102 : f02-f10+d≤1)
    (hr021 : f02-f21-d≤1) (hr120 : f12-f20-d≤1) : d=0 := by
  have h := two_head_step_bound f01 f10 f02 f20 f12 f21 1 d
    hx01 hx02 hx12 hl201 hl102 hr021 hr120
  linarith [h.2.1,h.2.2]

/-- `width=k-2`; telescoping the internal step bounds gives `hcursor`.
The endpoint pair is (0,1) initially and (1,0) finally. -/
theorem two_head_endpoint_bound (weight m width pairChange cursorChange : Rat)
    (hw : weight≤1) (hm : width+1≤m)
    (hpair : pairChange≤-weight)
    (hcursor : cursorChange≤width*(1-weight)) :
    weight*m+pairChange+cursorChange≤m-1 := by
  have hprod : 0≤(1-weight)*(m-width-1) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

#print axioms telescope
#print axioms head_weight_bound
#print axioms no_unit_head_potential
#print axioms two_head_step_bound
#print axioms two_head_unit_flat
#print axioms two_head_endpoint_bound
end LRX.LowerBoundPotentialBarrier
