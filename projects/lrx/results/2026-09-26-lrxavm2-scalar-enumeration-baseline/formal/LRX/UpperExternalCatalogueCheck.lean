import LRX.UpperExternalFamilies

/-! Small kernel computation for the external catalogue only.
This is not the scalar-row exclusion computation. -/
namespace LRX.UpperExternalFamilies

set_option maxRecDepth 4096
set_option maxHeartbeats 800000 in
theorem catalogue_card : catalogue.card = 88 := by decide +kernel

#print axioms catalogue_card
end LRX.UpperExternalFamilies
