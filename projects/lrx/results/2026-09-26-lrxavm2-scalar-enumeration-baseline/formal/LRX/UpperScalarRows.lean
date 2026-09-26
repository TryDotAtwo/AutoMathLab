import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Union
import Mathlib.Tactic.Common

/-! Uskov19 §§12.1,14, SHA8547daf9…: integer scalar rows and a specification
enumerator. Geometric necessity and the final exclusion are separate obligations.
No claim about arbitrary permutations is assumed by this module. -/
namespace LRX.UpperScalarRows

set_option maxRecDepth 2048

structure Row where
  t : Int
  p : Int
  f : Int
  eps : Int
  a : Int
  U : Int
  m : Int
  v : Int
  x : Int
  deriving DecidableEq, Repr

def Row.B (r : Row) : Int := r.a+r.t-(if 0<r.a then 1 else 0)
def Row.A (r : Row) : Int := 2*r.eps+r.p-r.f
def Row.L (r : Row) : Int := 2*r.m+r.p-r.a-r.v
def Row.M (r : Row) : Int := 2*(r.t-1)*(r.v-r.t)+r.a*r.v+r.a*(r.a-1)/2
def Row.T (r : Row) (k : Int) : Int := 2*r.B+r.m-r.U-2-r.M-r.eps-k
def Row.cap (r : Row) : Int := r.m+r.p-2
def Row.Q (r : Row) : Int := r.m*(r.m+r.p)
def Row.extSq (r : Row) : Int := (r.v-2*r.t+2)^2+4*(r.t-1)
def Row.extEnergy (r : Row) : Int := r.extSq-r.v%2
def Row.credit (r : Row) (k : Int) : Int := 4*(r.T k)^2+2*r.T k
def Row.fillEnergy (r : Row) (k : Int) : Int :=
  4*r.T k*(r.T k+(if r.a<r.f then 1 else 0))
def Row.need (r : Row) : Int := 2*(r.Q-r.eps)-4*r.U*(r.L-r.U)
def Row.gapSq (r : Row) : Int :=
  if r.x≤r.cap then r.x^2 else r.cap^2+(r.x-r.cap)^2

/-- The explicit integer ranges printed in U19 §12.1, before pruning. -/
def Bounds (r : Row) : Prop :=
  2≤r.t ∧ r.t≤12 ∧ 0≤r.p ∧ r.p≤1 ∧
  0≤r.f ∧ r.f≤r.t+5 ∧ 0≤r.eps ∧ r.eps≤3*r.t+6 ∧
  0≤r.a ∧ r.a≤r.f ∧ 1≤r.U ∧ r.U≤3*r.t+1 ∧
  2*r.t+r.a+1≤r.m ∧ r.m≤1379 ∧
  2*r.t≤r.v ∧ r.v≤r.m-r.a-1 ∧ 0≤r.x ∧ r.x≤r.L-4

/-- Direct mathematical inequalities, without the C++ square-root acceleration.
Every scalar pruning condition of §12.1 is explicit, including parity. -/
def Filters (k : Int) (r : Row) : Prop :=
  (3≤r.t → r.t^3-3*r.t^2+3*r.t+1≤r.m) ∧
  r.f^2≤4*r.eps+r.p ∧ r.f≤2*r.eps+r.p ∧
  k≤2*r.B+r.t-r.U-r.A ∧ (r.Q-r.eps)%2=0 ∧
  2*r.f+r.t^2+2*r.t-r.eps≤2*r.v ∧
  2*r.U≤r.L ∧ 0≤r.T k ∧
  r.need≤r.extEnergy+r.fillEnergy k ∧
  r.need≤r.gapSq+r.extSq ∧ r.need≤r.x+r.credit k+r.extSq ∧
  (r.x+r.v+r.a-1)^2+2*r.v-1+r.p-2*(r.credit k+r.extSq)≤2*r.A ∧
  (r.x+r.v+r.a)^2≤4*r.eps+r.p+2*r.fillEnergy k+2*r.extEnergy ∧
  r.x≤2*r.T k+r.f-r.a ∧
  (r.x+r.v)^2-2*(r.extSq+r.gapSq)+2*(r.x+r.v-1)*r.a+r.a^2+r.p≤2*r.A

def Admissible (k : Int) (r : Row) : Prop :=
  (k=1 ∨ k=2) ∧ Bounds r ∧ Filters k r

instance (r : Row) : Decidable (Bounds r) := by unfold Bounds; infer_instance
instance (k : Int) (r : Row) : Decidable (Filters k r) := by unfold Filters; infer_instance
instance (k : Int) (r : Row) : Decidable (Admissible k r) := by unfold Admissible; infer_instance

/-- A finite specification, not a proposed fast evaluation of this huge rectangle. -/
def box : Finset Row :=
  (Finset.Icc (2:Int) 12).biUnion fun t =>
  (Finset.Icc (0:Int) 1).biUnion fun p =>
  (Finset.Icc (0:Int) (t+5)).biUnion fun f =>
  (Finset.Icc (0:Int) (3*t+6)).biUnion fun eps =>
  (Finset.Icc (0:Int) f).biUnion fun a =>
  (Finset.Icc (1:Int) (3*t+1)).biUnion fun U =>
  (Finset.Icc (2*t+a+1) 1379).biUnion fun m =>
  (Finset.Icc (2*t) (m-a-1)).biUnion fun v =>
  (Finset.Icc (0:Int) (2*m+p-a-v-4)).image fun x => ⟨t,p,f,eps,a,U,m,v,x⟩

theorem mem_box (r : Row) : r∈box ↔ Bounds r := by
  rcases r with ⟨t,p,f,eps,a,U,m,v,x⟩
  simp only [box, Finset.mem_biUnion, Finset.mem_image, Finset.mem_Icc,
    Row.mk.injEq, Bounds, Row.L]
  aesop

def rows (k : Int) : Finset Row := box.filter (Admissible k)

/-- Soundness AND coverage: no admissible integer row is omitted. -/
theorem mem_rows (k : Int) (r : Row) : r∈rows k ↔ Admissible k r := by
  rw [rows, Finset.mem_filter, mem_box]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨h.2.1,h⟩

theorem range_nonnegative (r : Row) (h : Bounds r) :
    0≤r.m ∧ 0≤r.v ∧ 0≤r.cap ∧ r.x<2*r.cap := by
  rcases h with ⟨ht,ht',hp,hp',hf,hf',he,he',ha,ha',hu,hu',hm,hm',hv,hv',hx,hx'⟩
  dsimp [Row.L] at hx'
  dsimp [Row.cap]
  omega

/-- Any verified check on the finite enumerator transfers to all scalar rows.
This theorem does not assert that any particular check has already succeeded. -/
theorem of_rows (k : Int) (P : Row → Prop)
    (checked : ∀ r∈rows k, P r) : ∀ r, Admissible k r → P r := by
  intro r hr
  apply checked r
  rw [mem_rows]
  exact hr

#print axioms mem_box
#print axioms mem_rows
#print axioms range_nonnegative
#print axioms of_rows
end LRX.UpperScalarRows
