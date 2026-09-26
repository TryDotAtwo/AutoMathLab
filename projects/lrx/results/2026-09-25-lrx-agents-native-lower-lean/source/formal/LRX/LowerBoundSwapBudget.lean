import LRX.LowerBoundPaidProjection

/-! Actual X-budget in the same physical two-arc model. Integer inversion
potentials count every swap, including descending or repeated exchanges. -/
namespace LRX.LowerBoundSwapBudget
open scoped BigOperators
open LRX.BlockExchange LRX.LowerBoundFoldedTransport
open LRX.LowerBoundPaidProjection

def invPair (x y z w : Nat) : Int := if x<y ∧ w<z then 1 else 0

def inversions {j : Nat} (p : Equiv.Perm (Fin j)) : Int :=
  ∑ x : Fin j, ∑ y : Fin j, invPair x.val y.val (p x).val (p y).val

theorem scalar_swap_bound (x y z w c : Nat) :
    invPair x y (physicalSwapPosition c z) (physicalSwapPosition c w)-invPair x y z w≤
      if z=c ∧ w=c+1 then 1 else 0 := by
  unfold invPair physicalSwapPosition
  split_ifs <;> omega

theorem sum_at_position {j : Nat} (p : Equiv.Perm (Fin j)) (c : Fin j) :
    (∑ x : Fin j, if p x=c then (1 : Int) else 0)=1 := by
  rw [Equiv.sum_comp p (fun z => if z=c then (1 : Int) else 0)]
  simp

theorem exchange_inversions {j : Nat} {s t : State j} (h : Exchange s t) :
    inversions t.pos-inversions s.pos≤1 := by
  let c : Fin j := s.cursor
  let d : Fin j := ⟨s.cursor.val+1,h.1⟩
  have hp : ∀ x, (t.pos x).val=physicalSwapPosition s.cursor.val (s.pos x).val := h.2.2.2
  have hd : (∑ x : Fin j, ∑ y : Fin j,
      if s.pos x=c ∧ s.pos y=d then (1 : Int) else 0)=1 := by
    have hi : ∀ x : Fin j, (∑ y : Fin j,
      if s.pos x=c ∧ s.pos y=d then (1 : Int) else 0)=if s.pos x=c then 1 else 0 := by
      intro x
      by_cases hx : s.pos x=c
      · simp only [hx,true_and,ite_true]
        exact sum_at_position s.pos d
      · simp [hx]
    simp_rw [hi]
    exact sum_at_position s.pos c
  calc
    inversions t.pos-inversions s.pos =
      ∑ x : Fin j, ∑ y : Fin j,
        (invPair x.val y.val (t.pos x).val (t.pos y).val-
         invPair x.val y.val (s.pos x).val (s.pos y).val) := by
          simp only [inversions,Finset.sum_sub_distrib]
    _ ≤ ∑ x : Fin j, ∑ y : Fin j, if s.pos x=c ∧ s.pos y=d then (1 : Int) else 0 := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      rw [hp,hp]
      have he1 : (s.pos x).val=s.cursor.val ↔ s.pos x=c := by exact Fin.val_inj
      have he2 : (s.pos y).val=s.cursor.val+1 ↔ s.pos y=d := by
        change (s.pos y).val=d.val ↔ s.pos y=d
        exact Fin.val_inj
      simpa only [he1,he2] using scalar_swap_bound x.val y.val (s.pos x).val (s.pos y).val s.cursor.val
    _ = 1 := hd

def pairs (j : Nat) : Int := ∑ x : Fin j, ∑ y : Fin j, if x.val<y.val then 1 else 0

theorem pairs_double (j : Nat) : 2*pairs j=(j : Int)*((j : Int)-1) := by
  have hswap : (∑ x : Fin j, ∑ y : Fin j, if y.val<x.val then (1 : Int) else 0)=pairs j := by
    rw [Finset.sum_comm]
    rfl
  have hsum : (∑ x : Fin j, ∑ y : Fin j,
      ((if x.val<y.val then (1 : Int) else 0)+(if y.val<x.val then 1 else 0)))=2*pairs j := by
    simp only [Finset.sum_add_distrib]
    rw [hswap]
    change pairs j+pairs j=2*pairs j
    omega
  have hpair : ∀ x y : Fin j,
      (if x.val<y.val then (1 : Int) else 0)+(if y.val<x.val then 1 else 0)=
        1-(if x=y then 1 else 0) := by
    intro x y
    by_cases he : x=y
    · subst y; simp
    · have hv : x.val≠y.val := fun h => he (Fin.ext h)
      split_ifs <;> omega
  rw [←hsum]
  simp_rw [hpair]
  simp [Finset.sum_sub_distrib]
  ring1

theorem initial_inversions {j : Nat} (p : Equiv.Perm (Fin j))
    (hp : ∀ x, (p x).val=x.val) : inversions p=0 := by
  have hz : ∀ x y : Fin j, invPair x.val y.val (p x).val (p y).val=0 := by
    intro x y
    rw [hp,hp]
    unfold invPair
    split_ifs <;> omega
  simp [inversions,hz]

theorem reversed_inversions {j : Nat} (p : Equiv.Perm (Fin j))
    (hp : ∀ x, (p x).val+x.val+1=j) : 2*inversions p=(j : Int)*((j : Int)-1) := by
  have he : inversions p=pairs j := by
    unfold inversions pairs
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    have hx := hp x
    have hy := hp y
    unfold invPair
    split_ifs <;> omega
  rw [he,pairs_double]

def potential {a b : Nat} (s : TwoState a b) : Int := inversions s.posA+inversions s.posB

def xPrice : Op → Nat
  | .X => 1
  | .L | .R => 0

theorem step_inversion_bound {a b : Nat} (ha : 0<a) (hb : 0<b)
    {s t : TwoState a b} {op : Op} (h : LRX.LowerBoundPaidProjection.Step ha hb s op t) :
    potential t-potential s≤(xPrice op : Int) := by
  cases h with
  | left h => simp [potential,h.1,h.2.1,xPrice]
  | right h => simp [potential,h.1,h.2.1,xPrice]
  | exchangeA h _ _ hp =>
    have he := exchange_inversions h
    change inversions t.posA-inversions s.posA≤1 at he
    simp only [potential,hp,xPrice,Nat.cast_one]
    omega
  | exchangeB h _ _ hp =>
    have he := exchange_inversions h
    change inversions t.posB-inversions s.posB≤1 at he
    simp only [potential,hp,xPrice,Nat.cast_one]
    omega

theorem trace_inversion_bound {a b : Nat} (ha : 0<a) (hb : 0<b)
    {s t : TwoState a b} {w : List Op} (h : LRX.LowerBoundPaidProjection.Trace ha hb s w t) :
    potential t-potential s≤(exchanges w : Int) := by
  induction h with
  | nil => simp [exchanges]
  | @cons s m t op w hs ht ih =>
    have hstep := step_inversion_bound ha hb hs
    have hc : exchanges (op::w)=xPrice op+exchanges w := by cases op <;> simp [exchanges,xPrice]
    rw [hc]
    push_cast
    omega

/-- Every X is counted, including repeated and inversion-decreasing swaps. -/
theorem physical_swap_budget {a b : Nat} (ha : 0<a) (hb : 0<b)
    {s t : TwoState a b} {w : List Op} (h : PhysicalTrace s w t)
    (hsA : ∀ x, (s.posA x).val=x.val) (hsB : ∀ x, (s.posB x).val=x.val)
    (htA : ∀ x, (t.posA x).val+x.val+1=a)
    (htB : ∀ x, (t.posB x).val+x.val+1=b) :
    (a : Int)*((a : Int)-1)+(b : Int)*((b : Int)-1)≤2*(exchanges w : Int) := by
  have hbnd := trace_inversion_bound ha hb ((physical_trace_iff ha hb).mp h)
  have hs1 := initial_inversions s.posA hsA
  have hs2 := initial_inversions s.posB hsB
  have ht1 := reversed_inversions t.posA htA
  have ht2 := reversed_inversions t.posB htB
  unfold potential at hbnd
  rw [hs1,hs2] at hbnd
  omega

/-- Full N lower bound in the physical two-arc model, with no assumed X count,
no monotonicity hypothesis, no transport lower bound among assumptions. -/
theorem physical_two_block_total_lower {a b : Nat} (ha : 2≤a) (hb : 2≤b)
    {s t : TwoState a b} {w : List Op} (h : PhysicalTrace s w t)
    (hsA : ∀ x, (s.posA x).val=x.val) (hsB : ∀ x, (s.posB x).val=x.val)
    (htA : ∀ x, (t.posA x).val+x.val+1=a)
    (htB : ∀ x, (t.posB x).val+x.val+1=b)
    (hp : (s.cursor.val+t.cursor.val+2)%(a+b)=a) :
    (a+b)*(a+b-1)/2≤w.length := by
  have hr := (physical_two_block_rotation_lower ha hb h hsA hsB htA htB hp).2
  have hx := physical_swap_budget (by omega) (by omega) h hsA hsB htA htB
  have hc := every_letter_charged w
  have hrZ : (a : Int)*b≤(rotations w : Int) := by exact_mod_cast hr
  have hcZ : (rotations w : Int)+(exchanges w : Int)=(w.length : Int) := by exact_mod_cast hc
  have hZ : ((a : Int)+b)*((a : Int)+b-1)≤2*(w.length : Int) := by nlinarith
  have hn : ((a+b-1 : Nat) : Int)=(a : Int)+b-1 := by omega
  have hZ2 : ((a+b : Nat) : Int)*((a+b-1 : Nat) : Int)≤2*(w.length : Int) := by
    rw [Nat.cast_add,hn]
    exact hZ
  have hN : (a+b)*(a+b-1)≤2*w.length := by exact_mod_cast hZ2
  omega

#print axioms scalar_swap_bound
#print axioms exchange_inversions
#print axioms pairs_double
#print axioms trace_inversion_bound
#print axioms physical_swap_budget
#print axioms physical_two_block_total_lower
end LRX.LowerBoundSwapBudget
