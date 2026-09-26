import LRX.UpperScalarRows
import Mathlib.Tactic.Linarith

/-! Coverage of the C++ m and v bounds, including truncation toward zero.
All values are mathematical integers; absence of int64 overflow is not asserted here. -/
namespace LRX.UpperScalarRows

def Row.mLower (r : Row) : Int :=
  max (2*r.t+r.a+1) (if 3≤r.t then r.t^3-3*r.t^2+3*r.t+1 else 0)
def Row.vLower (r : Row) : Int :=
  max (2*r.t) ((2*r.f+r.t^2+2*r.t-r.eps+1).tdiv 2)
def Row.vUpper (r : Row) (k : Int) : Int :=
  min (r.m-r.a-1)
    ((2*r.B+r.m-r.U-2-k-r.eps+2*r.t*(r.t-1)-r.a*(r.a-1)/2).tdiv
      (2*(r.t-1)+r.a))

theorem ceil_half_tdiv_le (z v : Int) (hv : 1 ≤ v) (hz : z ≤ 2*v) :
    (z+1).tdiv 2 ≤ v := by
  rw [Int.tdiv_eq_ediv]
  have hs : Int.sign (2 : Int) = 1 := rfl
  rw [hs]
  split <;> omega

theorem triangular_div_agrees (a : Int) (ha : 0 ≤ a) :
    (a*(a-1)).tdiv 2 = a*(a-1)/2 := by
  apply Int.tdiv_eq_ediv_of_nonneg
  by_cases hz : a = 0
  · simp [hz]
  · have : 1 ≤ a := by omega
    nlinarith

/-- Every direct admissible row lies inside the accelerated m and v loops. -/
theorem admissible_mv_covered (k : Int) (r : Row) (h : Admissible k r) :
    r.mLower ≤ r.m ∧ r.m ≤ 1379 ∧ r.vLower ≤ r.v ∧ r.v ≤ r.vUpper k := by
  rcases h.2.1 with ⟨ht,ht',hp,hp',hf,hf',he,he',ha,ha',hu,hu',hm,hm',hv,hv',hx,hx'⟩
  rcases h.2.2 with ⟨hc,_,_,_,_,hd,_,hT,_⟩
  have hm0 : 0 ≤ r.m := by omega
  have hml : r.mLower ≤ r.m := by
    unfold Row.mLower
    rw [max_le_iff]
    refine ⟨hm, ?_⟩
    split_ifs with h3
    · exact hc h3
    · exact hm0
  have hvl : r.vLower ≤ r.v := by
    unfold Row.vLower
    exact max_le hv (ceil_half_tdiv_le _ _ (by omega) hd)
  have hden : 0 < 2*(r.t-1)+r.a := by omega
  have hprod : r.v*(2*(r.t-1)+r.a) ≤
      2*r.B+r.m-r.U-2-k-r.eps+2*r.t*(r.t-1)-r.a*(r.a-1)/2 := by
    dsimp [Row.T, Row.M] at hT
    nlinarith only [hT]
  have hvu : r.v ≤ r.vUpper k := by
    unfold Row.vUpper
    exact le_min hv' (Int.le_tdiv_of_mul_le hden hprod)
  exact ⟨hml,hm',hvl,hvu⟩

#print axioms ceil_half_tdiv_le
#print axioms triangular_div_agrees
#print axioms admissible_mv_covered
end LRX.UpperScalarRows
