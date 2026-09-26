import LRX.UpperScalarRows
import LRX.UpperScalarSqrt

/-! Equivalence of the two accelerated x intervals to the direct scalar constraints.
This does not evaluate the scalar enumeration or assert that its rows are excluded. -/
namespace LRX.UpperScalarRows
open LRX.UpperScalarSqrt

def Row.xLower (r : Row) (k : Int) (second : Bool) : Int :=
  max (if second then r.cap + ceilSqrt (r.need-r.extSq-r.cap^2)
       else ceilSqrt (r.need-r.extSq)) (r.need-r.extSq-r.credit k)

def Row.xUpper (r : Row) (k : Int) (second : Bool) : Int :=
  min (min (min (if second then r.L-4 else min r.cap (r.L-4))
    (floorSqrt (2*r.A-2*r.v+1-r.p+2*(r.credit k+r.extSq))-(r.v+r.a-1)))
    (floorSqrt (4*r.eps+r.p+2*r.fillEnergy k+2*r.extEnergy)-r.v-r.a))
    (2*r.T k+r.f-r.a)

def InXBranch (k : Int) (r : Row) (second : Bool) : Prop :=
  r.xLower k second ≤ r.x ∧ r.x ≤ r.xUpper k second

def XFilters (k : Int) (r : Row) : Prop :=
  r.need≤r.gapSq+r.extSq ∧
  r.need≤r.x+r.credit k+r.extSq ∧
  (r.x+r.v+r.a-1)^2+2*r.v-1+r.p-2*(r.credit k+r.extSq)≤2*r.A ∧
  (r.x+r.v+r.a)^2≤4*r.eps+r.p+2*r.fillEnergy k+2*r.extEnergy ∧
  r.x≤2*r.T k+r.f-r.a

theorem x_interval_iff (k : Int) (r : Row) (hb : Bounds r) :
    (InXBranch k r false ∨ InXBranch k r true) ↔ XFilters k r := by
  have hx : 0 ≤ r.x := by rcases hb with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,h,_⟩; exact h
  have hu : r.x ≤ r.L-4 := by rcases hb with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,h⟩; exact h
  have hs1 : 0 ≤ r.x+(r.v+r.a-1) := by
    rcases hb with ⟨ht,_,_,_,_,_,_,_,ha,_,_,_,_,_,hv,_,_,_⟩
    omega
  have hs2 : 0 ≤ r.x+(r.v+r.a) := by omega
  have hbranch := branch_union_iff r.x r.cap (r.need-r.extSq) (r.L-4) hx
  have hfloor1 := le_floorSqrt_iff (r.x+(r.v+r.a-1))
    (2*r.A-2*r.v+1-r.p+2*(r.credit k+r.extSq)) hs1
  have hfloor2 := le_floorSqrt_iff (r.x+(r.v+r.a))
    (4*r.eps+r.p+2*r.fillEnergy k+2*r.extEnergy) hs2
  have heq1 : r.x+(r.v+r.a-1) = r.x+r.v+r.a-1 := by omega
  have heq2 : r.x+(r.v+r.a) = r.x+r.v+r.a := by omega
  rw [heq1] at hfloor1
  rw [heq2] at hfloor2
  change _ ↔ (r.x ≤ r.L-4 ∧ r.need-r.extSq ≤ r.gapSq) at hbranch
  simp only [InXBranch, Row.xLower, Row.xUpper, Bool.false_eq_true,
    if_false, if_true, max_le_iff, le_min_iff]
  unfold XFilters
  omega

/-- Coverage of both accelerated x branches for every direct admissible row. -/
theorem admissible_x_covered (k : Int) (r : Row) (h : Admissible k r) :
    InXBranch k r false ∨ InXBranch k r true := by
  apply (x_interval_iff k r h.2.1).2
  rcases h.2.2 with ⟨_,_,_,_,_,_,_,_,_,h1,h2,h3,h4,h5,_⟩
  exact ⟨h1,h2,h3,h4,h5⟩

#print axioms x_interval_iff
#print axioms admissible_x_covered
end LRX.UpperScalarRows
