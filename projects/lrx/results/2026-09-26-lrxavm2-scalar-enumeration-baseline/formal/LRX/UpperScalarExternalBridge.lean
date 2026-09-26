import LRX.UpperScalarEnumeration
import LRX.UpperExternalFamilies

/-! An explicit pending certificate interface. No inhabitant of ScalarCapChecked
is supplied by this package, and no C++ output is imported as a proof. -/
namespace LRX.UpperScalarRows
open LRX.UpperExternalFamilies

def ScalarCapChecked (k : Int) : Prop :=
  ∀ r ∈ prunedRows k, r.v-2*(r.t-1) ≤ 5

/-- Conditional bridge from a verified scalar cap to external family coverage.
The validity/count/mass of the geometric external components must still be supplied. -/
theorem external_family_of_scalar_cap (k : Int) (r : Row)
    (checked : ScalarCapChecked k) (hr : Admissible k r)
    (ps : List (List Nat)) (hv : ∀ p ∈ ps, Valid p)
    (ht : (ps.length : Int) = r.t) (hm : (mass ps : Int) = r.v) :
    ps ∈ families r.t.toNat r.v.toNat := by
  have hc : r.v-2*(r.t-1) ≤ 5 := by
    apply checked r
    rw [mem_prunedRows]
    exact hr
  have htwo : 2 ≤ r.t := hr.2.1.1
  have hcap : mass ps - 2*(ps.length-1) ≤ 5 := by omega
  have et : r.t.toNat = ps.length := by omega
  have ev : r.v.toNat = mass ps := by omega
  rw [et,ev]
  exact bounded_valid_family_covered ps hv hcap

#print axioms external_family_of_scalar_cap
end LRX.UpperScalarRows
