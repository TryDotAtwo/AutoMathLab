import LRX.BlockExchange
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring.Basic
import Mathlib.Data.Fintype.BigOperators

/-! Concrete folded coordinates for B's pointed-block transport argument.
All coordinates and windings are integers. No X on the external cut is allowed.
This file does not yet assert the original Cayley-graph diameter theorem. -/
namespace LRX.LowerBoundFoldedTransport
open scoped BigOperators

def folded (z c h : Int) : Int := z - (if c < z then 1 else 0) + h

theorem folded_exchange (c z h : Int) :
    folded (if z=c then c+1 else if z=c+1 then c else z) c h = folded z c h := by
  unfold folded
  split_ifs <;> omega

theorem folded_left_internal (z c h : Int) :
    folded z (c+1) h-folded z c h = if z=c+1 then 1 else 0 := by
  unfold folded
  split_ifs <;> omega

theorem folded_left_wrap (j z h : Int) (hz : 0≤z) (hzj : z<j) :
    folded z 0 (h+1)-folded z (j-1) h = if z=0 then 1 else 0 := by
  unfold folded
  split_ifs <;> omega

theorem reflected_endpoints (j x u h : Int) (hu : 0≤u) (huj : u≤j-2)
    (hx : 0≤x) (hxj : x<j) :
    folded (j-1-x) (j-2-u) h + folded x u 0 = j-2+h := by
  unfold folded
  split_ifs <;> omega

theorem external_coordinates (j z h : Int) (hz : z<j) :
    folded z (j-1) h = z+h := by
  unfold folded
  have hn : ¬ j-1<z := by omega
  simp [hn]

/-- L1 distance on actual labelled coordinate vectors. -/
def distance {j : Nat} (f g : Fin j → Int) : Int := ∑ x, |g x-f x|

theorem distance_refl {j : Nat} (f : Fin j → Int) : distance f f=0 := by
  simp [distance]

theorem distance_symm {j : Nat} (f g : Fin j → Int) : distance f g=distance g f := by
  unfold distance
  apply Finset.sum_congr rfl
  intro x _
  exact abs_sub_comm _ _

theorem distance_triangle {j : Nat} (f g h : Fin j → Int) :
    distance f h≤distance f g+distance g h := by
  unfold distance
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  simpa [add_comm] using abs_sub_le (h x) (g x) (f x)

structure State (j : Nat) where
  pos : Equiv.Perm (Fin j)
  cursor : Fin j
  winding : Int

def coords {j : Nat} (s : State j) (x : Fin j) : Int :=
  folded (s.pos x).val s.cursor.val s.winding

/-- Literal physical L: same labelled array, cursor+1, with explicit wrap. -/
def Left {j : Nat} (s t : State j) : Prop :=
  t.pos=s.pos ∧
  ((t.cursor.val=s.cursor.val+1 ∧ t.winding=s.winding) ∨
   (s.cursor.val+1=j ∧ t.cursor.val=0 ∧ t.winding=s.winding+1))

/-- Literal internal adjacent X, explicitly excluding the external cut. -/
def Exchange {j : Nat} (s t : State j) : Prop :=
  s.cursor.val+1<j ∧ t.cursor=s.cursor ∧ t.winding=s.winding ∧
  ∀ x, (t.pos x).val = if (s.pos x).val=s.cursor.val then s.cursor.val+1
    else if (s.pos x).val=s.cursor.val+1 then s.cursor.val else (s.pos x).val

theorem left_delta {j : Nat} {s t : State j} (h : Left s t) (x : Fin j) :
    coords t x-coords s x = if (s.pos x)=t.cursor then 1 else 0 := by
  obtain ⟨hp,hi|hw⟩ := h
  · obtain ⟨hc,hh⟩ := hi
    have he : ((s.pos x).val : Int)=(s.cursor.val : Int)+1 ↔ s.pos x=t.cursor := by
      constructor <;> intro e
      · apply Fin.ext; omega
      · have := congrArg Fin.val e; omega
    simp only [coords,hp,hh]
    have hci : (t.cursor.val : Int)=(s.cursor.val : Int)+1 := by omega
    rw [hci,folded_left_internal]
    simp only [he]
  · obtain ⟨hj,hc,hh⟩ := hw
    have hci : (s.cursor.val : Int)=(j : Int)-1 := by omega
    have he : ((s.pos x).val : Int)=0 ↔ s.pos x=t.cursor := by
      constructor <;> intro e
      · apply Fin.ext; omega
      · have := congrArg Fin.val e; omega
    simp only [coords,hp,hh,hc,Nat.cast_zero,hci]
    rw [folded_left_wrap (j : Int) _ _ (by omega) (by exact_mod_cast (s.pos x).isLt)]
    simp only [he]

theorem left_distance {j : Nat} {s t : State j} (h : Left s t) :
    distance (coords s) (coords t)=1 := by
  unfold distance
  simp_rw [left_delta h]
  have hab : ∀ x : Fin j, |(if s.pos x=t.cursor then 1 else 0 : Int)| =
      if s.pos x=t.cursor then 1 else 0 := by intro x; split_ifs <;> norm_num
  simp_rw [hab]
  have he : (∑ x : Fin j, if s.pos x=t.cursor then (1 : Int) else 0)=
      ∑ y : Fin j, if y=t.cursor then (1 : Int) else 0 := by
    exact Equiv.sum_comp s.pos (fun y => if y=t.cursor then (1 : Int) else 0)
  rw [he]
  simp

theorem exchange_coords {j : Nat} {s t : State j} (h : Exchange s t) :
    coords t=coords s := by
  obtain ⟨_,hc,hh,hp⟩ := h
  funext x
  simp only [coords,hc,hh,hp]
  push_cast
  convert folded_exchange (s.cursor.val : Int) ((s.pos x).val : Int) s.winding using 1 <;>
    split_ifs <;> simp_all <;> omega

inductive Step {j : Nat} : State j → LRX.BlockExchange.Op → State j → Prop where
  | left {s t} : Left s t → Step s .L t
  | right {s t} : Left t s → Step s .R t
  | exchange {s t} : Exchange s t → Step s .X t

def price : LRX.BlockExchange.Op → Nat
  | .L | .R => 1
  | .X => 0

def rotations : List LRX.BlockExchange.Op → Nat
  | [] => 0
  | op::w => price op+rotations w

inductive Trace {j : Nat} : State j → List LRX.BlockExchange.Op → State j → Prop where
  | nil (s) : Trace s [] s
  | cons {s t v op w} : Step s op t → Trace t w v → Trace s (op::w) v

theorem step_distance {j : Nat} {s t : State j} {op} (h : Step s op t) :
    distance (coords s) (coords t)=(price op : Int) := by
  cases h with
  | left h => exact left_distance h
  | right h => rw [distance_symm]; exact left_distance h
  | exchange h => rw [exchange_coords h,distance_refl]; rfl

theorem trace_transport {j : Nat} {s t : State j} {w} (h : Trace s w t) :
    distance (coords s) (coords t)≤(rotations w : Int) := by
  induction h with
  | nil s => simp [rotations,distance_refl]
  | @cons s v t op w hs ht ih =>
    have hd := distance_triangle (coords s) (coords v) (coords t)
    rw [step_distance hs] at hd
    simp only [rotations,Nat.cast_add]
    omega

/-- Absolute-value geometry, with a literal sum over all physical positions. -/
def spread (j : Nat) (t : Int) : Int := ∑ i ∈ Finset.range j, |2*(i : Int)-t|

theorem spread_two (j : Nat) (t : Int) :
    spread (j+2) t = spread j (t-2)+|t|+|2*((j : Int)+1)-t| := by
  unfold spread
  rw [Finset.sum_range_succ,Finset.sum_range_succ']
  have he : (∑ i ∈ Finset.range j, |2*((i+1 : Nat) : Int)-t|)=
      ∑ i ∈ Finset.range j, |2*(i : Int)-(t-2)| := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    push_cast
    ring1
  rw [he]
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,mul_zero,zero_sub,abs_neg]

theorem spread_step_bound (j : Nat) (t : Int) :
    spread j (t-2)+2*((j : Int)+1)≤spread (j+2) t := by
  rw [spread_two]
  have h := abs_sub_le (2*((j : Int)+1)) t 0
  have hp : |2*((j : Int)+1)|=2*((j : Int)+1) := abs_of_nonneg (by omega)
  simp only [sub_zero,hp] at h
  omega

theorem spread_even (k : Nat) (t : Int) :
    2*(k : Int)^2≤spread (2*k) t := by
  induction k generalizing t with
  | zero => simp [spread]
  | succ k ih =>
    have h := spread_step_bound (2*k) t
    have h0 := ih (t-2)
    have he : 2*(k+1)=2*k+2 := by omega
    rw [he]
    push_cast at h ⊢
    nlinarith

theorem spread_odd (k : Nat) (t : Int) :
    2*(k : Int)*((k : Int)+1)≤spread (2*k+1) t := by
  induction k generalizing t with
  | zero => simp [spread]
  | succ k ih =>
    have h := spread_step_bound (2*k+1) t
    have h0 := ih (t-2)
    have he : 2*(k+1)+1=(2*k+1)+2 := by omega
    rw [he]
    push_cast at h ⊢
    nlinarith

theorem spread_lower (j : Nat) (t : Int) :
    ((j*j/2 : Nat) : Int)≤spread j t := by
  have hm := Nat.mod_add_div j 2
  have hr := Nat.mod_lt j (by omega : 0<2)
  by_cases he : j%2=0
  · have hj : j=2*(j/2) := by omega
    have h := spread_even (j/2) t
    have hnum : j*j/2=2*(j/2)^2 := by
      have hsq : j*j=2*(2*(j/2)^2) := by nlinarith [hj]
      omega
    rw [hnum]
    push_cast
    rw [←hj] at h
    exact h
  · have hj : j=2*(j/2)+1 := by omega
    have h := spread_odd (j/2) t
    have hnum : j*j/2=2*(j/2)*(j/2+1) := by
      have hsq : j*j=2*(2*(j/2)*(j/2+1))+1 := by nlinarith [hj]
      omega
    rw [hnum]
    push_cast
    rw [←hj] at h
    exact h

/-- Geometry is independent of the physical permutation at the waypoint. -/
theorem permutation_spread {j : Nat} (p : Equiv.Perm (Fin j)) (t : Int) :
    ((j*j/2 : Nat) : Int)≤∑ x : Fin j, |2*((p x).val : Int)-t| := by
  rw [Equiv.sum_comp p (fun y : Fin j => |2*(y.val : Int)-t|)]
  rw [Fin.sum_univ_eq_sum_range (fun i : Nat => |2*(i : Int)-t|) j]
  exact spread_lower j t

/-- Actual two trace segments through the external cursor. The endpoint
coordinate-sum condition will be derived from literal reversal below. -/
theorem waypoint_transport {j : Nat} {s m t : State j} {u v}
    (hu : Trace s u m) (hv : Trace m v t) (hm : m.cursor.val+1=j)
    (K : Int) (he : ∀ x, coords s x+coords t x=K) :
    ((j*j/2 : Nat) : Int)≤(rotations u+rotations v : Nat) := by
  have h1 := trace_transport hu
  have h2 := trace_transport hv
  have hgeo := permutation_spread m.pos (K-2*m.winding)
  have hmc : (m.cursor.val : Int)=(j : Int)-1 := by omega
  have hcoord : ∀ x, coords m x=(m.pos x).val+m.winding := by
    intro x
    unfold coords
    rw [hmc,external_coordinates _ _ _ (by exact_mod_cast (m.pos x).isLt)]
  have hmid : (∑ x : Fin j, |2*((m.pos x).val : Int)-(K-2*m.winding)|)≤
      distance (coords s) (coords m)+distance (coords m) (coords t) := by
    unfold distance
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    have hx := he x
    have htri := abs_sub_le (coords m x-coords s x) 0 (coords t x-coords m x)
    simp only [sub_zero,zero_sub,abs_neg] at htri
    have hxid : coords m x-coords s x-(coords t x-coords m x)=
        2*((m.pos x).val : Int)-(K-2*m.winding) := by rw [hcoord]; omega
    rw [hxid] at htri
    exact htri
  push_cast
  omega

/-- Literal initial identity and final block reversal, with reflected internal
cursor endpoints. No assumption about intermediate swaps or their count. -/
theorem internal_reversal_transport {j : Nat} {s m t : State j} {u v}
    (hu : Trace s u m) (hv : Trace m v t) (hm : m.cursor.val+1=j)
    (hstart : ∀ x, (s.pos x).val=x.val)
    (hend : ∀ x, (t.pos x).val+x.val+1=j)
    (hc : s.cursor.val+t.cursor.val+2=j) :
    ((j*j/2 : Nat) : Int)≤(rotations u+rotations v : Nat) := by
  apply waypoint_transport hu hv hm ((j : Int)-2+s.winding+t.winding)
  intro x
  have hs := hstart x
  have ht := hend x
  unfold coords folded
  split_ifs <;> omega

/-- External initial and final cursors; no waypoint condition is necessary. -/
theorem external_reversal_transport {j : Nat} {s t : State j} {w}
    (hw : Trace s w t)
    (hstart : ∀ x, (s.pos x).val=x.val)
    (hend : ∀ x, (t.pos x).val+x.val+1=j)
    (hs : s.cursor.val+1=j) (ht : t.cursor.val+1=j) :
    ((j*j/2 : Nat) : Int)≤(rotations w : Nat) := by
  have hb := trace_transport hw
  have hgeo := permutation_spread (Equiv.refl (Fin j))
    ((j : Int)-1+t.winding-s.winding)
  have hdist : distance (coords s) (coords t)=
      ∑ x : Fin j, |2*(x.val : Int)-((j : Int)-1+t.winding-s.winding)| := by
    unfold distance
    apply Finset.sum_congr rfl
    intro x _
    have hc1 : (s.cursor.val : Int)=(j : Int)-1 := by omega
    have hc2 : (t.cursor.val : Int)=(j : Int)-1 := by omega
    unfold coords
    rw [hc1,hc2,external_coordinates _ _ _ (by exact_mod_cast (t.pos x).isLt),
      external_coordinates _ _ _ (by exact_mod_cast (s.pos x).isLt)]
    have h1 := hstart x
    have h2 := hend x
    have hh : ((t.pos x).val : Int)+t.winding-((s.pos x).val+s.winding)=
      -(2*(x.val : Int)-((j : Int)-1+t.winding-s.winding)) := by omega
    rw [hh,abs_neg]
  rw [hdist] at hb
  simpa only [Equiv.refl_apply] using le_trans hgeo hb

theorem rotations_append (u v : List LRX.BlockExchange.Op) :
    rotations (u++v)=rotations u+rotations v := by
  induction u with
  | nil => simp [rotations]
  | cons op u ih => simp [rotations,ih,Nat.add_assoc]

/-- Full pointed-block lemma: a literal complete reversal along one word,
with external endpoints OR reflected internal endpoints and an actual external
visit splitting that same word. This is not a theorem about unrestricted X. -/
theorem pointed_reversal_transport {j : Nat} {s t : State j} {w}
    (hw : Trace s w t)
    (hstart : ∀ x, (s.pos x).val=x.val)
    (hend : ∀ x, (t.pos x).val+x.val+1=j)
    (hphase : (s.cursor.val+1=j ∧ t.cursor.val+1=j) ∨
      (s.cursor.val+t.cursor.val+2=j ∧
        ∃ (m : State j) (u v : List LRX.BlockExchange.Op), w=u++v ∧
          Trace s u m ∧ Trace m v t ∧ m.cursor.val+1=j)) :
    j*j/2≤rotations w := by
  rcases hphase with ⟨hs,ht⟩ | ⟨hc,m,u,v,he,hu,hv,hm⟩
  · have h := external_reversal_transport hw hstart hend hs ht
    exact_mod_cast h
  · have h := internal_reversal_transport hu hv hm hstart hend hc
    rw [he,rotations_append]
    exact_mod_cast h

#print axioms folded_exchange
#print axioms folded_left_internal
#print axioms folded_left_wrap
#print axioms reflected_endpoints
#print axioms external_coordinates
#print axioms left_distance
#print axioms exchange_coords
#print axioms trace_transport
#print axioms spread_lower
#print axioms permutation_spread
#print axioms waypoint_transport
#print axioms internal_reversal_transport
#print axioms external_reversal_transport
#print axioms pointed_reversal_transport
end LRX.LowerBoundFoldedTransport
