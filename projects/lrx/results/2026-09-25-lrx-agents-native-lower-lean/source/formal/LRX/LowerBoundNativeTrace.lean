import LRX.LowerBoundSwapBudget
import LRX.Cycle11WordSymmetry
import LRX.LowerBoundCyclicContiguity
import Mathlib.Data.List.Rotate
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Logic.Equiv.Fin.Basic

/-! Explicit native list interpretation of the two-arc physical states.
Includes shortest-word arc extraction, actual trace construction and endpoint
phase derivation. The remaining general lower-bound branches have class size 0/1. -/
namespace LRX.LowerBoundNativeTrace
open LRX.BlockExchange LRX.LowerBoundPaidProjection
open LRX.LowerBoundNoRepeat LRX.LowerBoundCyclicContiguity
open LRX.Cycle11StructuralBridge LRX.Cycle11TwoLabelRepair
variable {a b : Nat}
abbrev Label (a b : Nat) := Sum (Fin a) (Fin b)

def color : Label a b → Bool
  | .inl _ => false
  | .inr _ => true

def Represents (s : TwoState a b) (xs : List (Label a b)) : Prop :=
  xs.Nodup ∧ xs.length=a+b ∧
  ∀ (i : Nat) (hi : i<xs.length),
    physicalPosition s xs[i]=(s.cursor.val+i)%(a+b)

theorem position_injective (s : TwoState a b) : Function.Injective (physicalPosition s) := by
  intro x y h
  cases x with
  | inl x => cases y with
    | inl y => exact congrArg Sum.inl (s.posA.injective (Fin.ext h))
    | inr y => simp only [physicalPosition] at h; have := (s.posA x).isLt; omega
  | inr x => cases y with
    | inl y => simp only [physicalPosition] at h; have := (s.posA y).isLt; omega
    | inr y =>
      apply congrArg Sum.inr
      apply s.posB.injective
      apply Fin.ext
      simp only [physicalPosition] at h
      omega

theorem left_rotate (xs : List α) : left xs=xs.rotate 1 := by
  cases xs <;> simp [left]

theorem represents_rotate {s t : TwoState a b} {xs : List (Label a b)}
    (h : Represents s xs) (k : Nat)
    (hp : ∀ x, physicalPosition t x=physicalPosition s x)
    (hc : t.cursor.val=(s.cursor.val+k)%(a+b)) :
    Represents t (xs.rotate k) := by
  refine ⟨(List.rotate_perm xs k).nodup_iff.mpr h.1,by simpa using h.2.1,?_⟩
  intro i hi
  rw [List.getElem_rotate,hp,h.2.2]
  simp only [h.2.1,hc]
  rw [Nat.add_mod_mod,Nat.mod_add_mod]
  congr 1; omega

def next (s : TwoState a b) : TwoState a b where
  posA := s.posA
  posB := s.posB
  cursor := ⟨(s.cursor.val+1)%(a+b),Nat.mod_lt _ (by have := s.cursor.isLt; omega)⟩
  winding := s.winding + if s.cursor.val+1=a+b then 1 else 0

def prev (s : TwoState a b) : TwoState a b where
  posA := s.posA
  posB := s.posB
  cursor := ⟨if s.cursor.val=0 then a+b-1 else s.cursor.val-1,by
    have := s.cursor.isLt; split_ifs <;> omega⟩
  winding := s.winding - if s.cursor.val=0 then 1 else 0

theorem next_left (s : TwoState a b) : Left s (next s) := by
  refine ⟨rfl,rfl,?_⟩
  have hc := s.cursor.isLt
  by_cases h : s.cursor.val+1=a+b
  · right; simp [next,h]
  · left; simp [next,h,Nat.mod_eq_of_lt (by omega : s.cursor.val+1<a+b)]

theorem prev_left (s : TwoState a b) : Left (prev s) s := by
  refine ⟨rfl,rfl,?_⟩
  have hc := s.cursor.isLt
  by_cases h : s.cursor.val=0
  · right; simp [prev,h]; omega
  · left; simp [prev,h]; omega

theorem right_rotate (xs : List α) (hn : 0<xs.length) :
    right xs=xs.rotate (xs.length-1) := by
  have h := congrArg (fun ys : List α => ys.rotate (xs.length-1))
    (LRX.ReducedPrice.left_right xs)
  rw [left_rotate,List.rotate_rotate] at h
  have hl : (right xs).length=xs.length := (step_perm .R xs).length_eq
  have he : 1+(xs.length-1)=(right xs).length := by omega
  rw [he,List.rotate_length] at h
  exact h

theorem represents_next {s : TwoState a b} {xs : List (Label a b)}
    (h : Represents s xs) : Represents (next s) (left xs) := by
  rw [left_rotate]
  exact represents_rotate h 1 (fun _ => rfl) rfl

theorem represents_prev {s : TwoState a b} {xs : List (Label a b)}
    (h : Represents s xs) : Represents (prev s) (right xs) := by
  have hn : 0<xs.length := by have := s.cursor.isLt; have := h.2.1; omega
  rw [right_rotate xs hn]
  apply represents_rotate (t := prev s) h (xs.length-1) (fun x => by cases x <;> rfl)
  have hc := s.cursor.isLt
  simp only [prev,h.2.1]
  by_cases hz : s.cursor.val=0
  · simp [hz,Nat.mod_eq_of_lt (by omega : a+b-1<a+b)]
  · simp only [hz,ite_false]
    have he : s.cursor.val+(a+b-1)=(s.cursor.val-1)+(a+b) := by omega
    rw [he,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega : s.cursor.val-1<a+b)]

def exchangeState (s : TwoState a b) (x y : Label a b) : TwoState a b :=
  match x,y with
  | .inl x,.inl y => {s with posA := (Equiv.swap x y).trans s.posA}
  | .inr x,.inr y => {s with posB := (Equiv.swap x y).trans s.posB}
  | _,_ => s

theorem exchangeState_position (s : TwoState a b) (x y z : Label a b)
    (hc : color x=color y) :
    physicalPosition (exchangeState s x y) z=physicalPosition s (Equiv.swap x y z) := by
  cases x <;> cases y <;> cases z <;>
    simp_all [color,exchangeState,physicalPosition,Equiv.swap_apply_def,Equiv.trans_apply] <;>
    split_ifs <;> rfl

theorem exchangeState_cursor (s : TwoState a b) (x y : Label a b) :
    (exchangeState s x y).cursor=s.cursor ∧ (exchangeState s x y).winding=s.winding := by
  cases x <;> cases y <;> exact ⟨rfl,rfl⟩

theorem represents_exchange {s : TwoState a b} {x y : Label a b}
    {tail : List (Label a b)} (h : Represents s (x::y::tail)) (hc : color x=color y) :
    Represents (exchangeState s x y) (y::x::tail) := by
  have he : y::x::tail=(x::y::tail).map (Equiv.swap x y) :=
    actual_head_swap x y (x::y::tail) h.1 (Or.inl ⟨tail,rfl⟩)
  rw [he]
  refine ⟨h.1.map (Equiv.swap x y).injective,by simpa using h.2.1,?_⟩
  intro i hi
  rw [List.getElem_map,exchangeState_position s x y _ hc,Equiv.swap_apply_self]
  rw [(exchangeState_cursor s x y).1]
  exact h.2.2 i (by simpa using hi)

theorem monochromatic_internal (ha : 0<a) (hb : 0<b) {s : TwoState a b} {x y : Label a b}
    {tail : List (Label a b)} (h : Represents s (x::y::tail)) (hc : color x=color y) :
    s.cursor.val+1<a+b ∧ s.cursor.val+1≠a := by
  have h0 := h.2.2 0 (by simp)
  have h1 := h.2.2 1 (by simp)
  have hlt := s.cursor.isLt
  simp only [List.getElem_cons_zero,Nat.add_zero,Nat.mod_eq_of_lt hlt] at h0
  simp only [List.getElem_cons_succ,List.getElem_cons_zero] at h1
  cases x with
  | inl x => cases y with
    | inl y =>
      simp only [physicalPosition] at h0 h1
      have hx := (s.posA x).isLt
      have hy := (s.posA y).isLt
      have hab : s.cursor.val+1<a+b := by omega
      rw [Nat.mod_eq_of_lt hab] at h1
      omega
    | inr y => simp [color] at hc
  | inr x => cases y with
    | inl y => simp [color] at hc
    | inr y =>
      simp only [physicalPosition] at h0 h1
      have hx := (s.posB x).isLt
      have hy := (s.posB y).isLt
      by_cases he : s.cursor.val+1=a+b
      · rw [he,Nat.mod_self] at h1
        omega
      · constructor <;> omega

theorem swap_positions (s : TwoState a b) (x y z : Label a b)
    (hx : physicalPosition s x=s.cursor.val)
    (hy : physicalPosition s y=s.cursor.val+1) :
    physicalPosition s (Equiv.swap x y z)=physicalSwapPosition s.cursor.val (physicalPosition s z) := by
  by_cases hzx : z=x
  · subst z; rw [Equiv.swap_apply_left]; simp [physicalSwapPosition,hx,hy]
  · by_cases hzy : z=y
    · subst z; rw [Equiv.swap_apply_right]; simp [physicalSwapPosition,hx,hy]
    · rw [Equiv.swap_apply_of_ne_of_ne hzx hzy]
      have hn0 : physicalPosition s z≠s.cursor.val := by
        intro he; exact hzx (position_injective s (he.trans hx.symm))
      have hn1 : physicalPosition s z≠s.cursor.val+1 := by
        intro he; exact hzy (position_injective s (he.trans hy.symm))
      simp [physicalSwapPosition,hn0,hn1]

theorem exchange_physical (ha : 0<a) (hb : 0<b) {s : TwoState a b}
    {x y : Label a b} {tail : List (Label a b)}
    (h : Represents s (x::y::tail)) (hc : color x=color y) :
    PhysicalX s (exchangeState s x y) := by
  have hi := monochromatic_internal ha hb h hc
  refine ⟨(exchangeState_cursor s x y).1,(exchangeState_cursor s x y).2,hi.1,hi.2,?_⟩
  intro z
  rw [exchangeState_position s x y z hc]
  apply swap_positions
  · have hh := h.2.2 0 (by simp)
    change physicalPosition s x=(s.cursor.val+0)%(a+b) at hh
    simpa only [Nat.add_zero,Nat.mod_eq_of_lt s.cursor.isLt] using hh
  · have hh := h.2.2 1 (by simp)
    change physicalPosition s y=(s.cursor.val+1)%(a+b) at hh
    simpa only [Nat.mod_eq_of_lt hi.1] using hh

/-- Existence of the next physical state is proved from the actual native
head pair. No PhysicalStep or PhysicalTrace is a premise. -/
theorem native_step_lift (ha : 0<a) (hb : 0<b) {s : TwoState a b}
    {xs : List (Label a b)} (h : Represents s xs) (op : Op)
    (hm : op=.X → ∀ x y tail, xs=x::y::tail → color x=color y) :
    ∃ t, PhysicalStep s op t ∧ Represents t (step op xs) := by
  cases op with
  | L => exact ⟨next s,PhysicalStep.left (next_left s),represents_next h⟩
  | R => exact ⟨prev s,PhysicalStep.right (prev_left s),represents_prev h⟩
  | X =>
    cases xs with
    | nil => have := h.2.1; simp at this; omega
    | cons x xs => cases xs with
      | nil => have := h.2.1; simp at this; omega
      | cons y tail =>
        have hc := hm rfl x y tail rfl
        exact ⟨exchangeState s x y,PhysicalStep.exchange (exchange_physical ha hb h hc),
          represents_exchange h hc⟩

/-- Lift the very same paid native word; no letters are inserted or removed.
The only trace restriction is the native monochromatic-head property. -/
theorem native_trace_lift (ha : 0<a) (hb : 0<b) {s : TwoState a b}
    {xs : List (Label a b)} (h : Represents s xs) (w : List Op)
    (hm : MonoTrace color w xs) :
    ∃ t, PhysicalTrace s w t ∧ Represents t (run w xs) := by
  induction w generalizing s xs with
  | nil => exact ⟨s,PhysicalTrace.nil s,h⟩
  | cons op w ih =>
    obtain ⟨m,hs,hr⟩ := native_step_lift ha hb h op (by
      intro he x y tail ht
      subst op
      exact hm [] w x y rfl (Or.inl ⟨tail,ht⟩))
    obtain ⟨t,hw,ht⟩ := ih hr (mono_tail color op w xs hm)
    exact ⟨t,PhysicalTrace.cons hs hw,ht⟩

def mirrorIndex (n i : Nat) : Nat := if i=0 then 1 else if i=1 then 0 else n+1-i

theorem mirrorIndex_lt {n i : Nat} (hn : 2≤n) (hi : i<n) : mirrorIndex n i<n := by
  unfold mirrorIndex; split_ifs <;> omega

theorem mirrorIndex_involutive {n i : Nat} (_hn : 2≤n) (hi : i<n) :
    mirrorIndex n (mirrorIndex n i)=i := by
  by_cases h0 : i=0
  · subst i; simp [mirrorIndex]
  by_cases h1 : i=1
  · subst i; simp [mirrorIndex]
  have h2 : n+1-i≠0 := by omega
  have h3 : n+1-i≠1 := by omega
  simp only [mirrorIndex,h0,h1,h2,h3,ite_false]
  omega

theorem mirrorIndex_sum {n i : Nat} (hn : 2≤n) (hi : i<n) :
    (i+mirrorIndex n i)%n=1 := by
  unfold mirrorIndex
  split_ifs with h0 h1
  · subst i; simp [Nat.mod_eq_of_lt (by omega : 1<n)]
  · subst i; simp [Nat.mod_eq_of_lt (by omega : 1<n)]
  · have he : i+(n+1-i)=n+1 := by omega
    rw [he,Nat.add_mod_left,Nat.mod_eq_of_lt (by omega : 1<n)]

theorem reflect_length (xs : List α) : (LRX.Cycle11WordSymmetry.reflect xs).length=xs.length := by
  cases xs with
  | nil => rfl
  | cons x xs => cases xs <;> simp [LRX.Cycle11WordSymmetry.reflect]

theorem reflect_get (xs : List α) (hn : 2≤xs.length) (i : Nat) (hi : i<xs.length) :
    (LRX.Cycle11WordSymmetry.reflect xs)[i]'(by rw [reflect_length]; exact hi)=
    xs[mirrorIndex xs.length i]'(mirrorIndex_lt hn hi) := by
  cases xs with
  | nil => simp at hn
  | cons x xs => cases xs with
    | nil => simp at hn
    | cons y tail =>
      cases i with
      | zero => simp [LRX.Cycle11WordSymmetry.reflect,mirrorIndex]
      | succ i => cases i with
        | zero => simp [LRX.Cycle11WordSymmetry.reflect,mirrorIndex]
        | succ i =>
          simp only [LRX.Cycle11WordSymmetry.reflect,List.getElem_cons_succ]
          rw [List.getElem_reverse]
          simp only [mirrorIndex,List.length_cons]
          simp only [show i+1+1≠0 by omega,show i+1+1≠1 by omega,ite_false]
          have he : tail.length+1+1+1-(i+1+1)=(tail.length-1-i)+2 := by
            simp only [List.length_cons] at hi
            omega
          simp only [he,List.getElem_cons_succ]

theorem reflected_position_sum {s t : TwoState a b} {xs : List (Label a b)}
    (hn : 2≤a+b) (hs : Represents s xs)
    (ht : Represents t (LRX.Cycle11WordSymmetry.reflect xs))
    (hall : ∀ x, x∈xs) (x : Label a b) :
    (physicalPosition t x+physicalPosition s x)%(a+b)=
      (s.cursor.val+t.cursor.val+1)%(a+b) := by
  obtain ⟨i,hi,hx⟩ := List.mem_iff_getElem.mp (hall x)
  have hn' : 2≤xs.length := by rw [hs.2.1]; exact hn
  let j := mirrorIndex xs.length i
  have hj : j<xs.length := mirrorIndex_lt hn' hi
  have hget : (LRX.Cycle11WordSymmetry.reflect xs)[j]'(by rw [reflect_length]; exact hj)=x := by
    rw [reflect_get xs hn' j hj]
    simpa only [j,mirrorIndex_involutive hn' hi] using hx
  have hsp := hs.2.2 i hi
  have htp := ht.2.2 j (by rw [reflect_length]; exact hj)
  rw [hx] at hsp
  rw [hget] at htp
  have hij : (i+j)%(a+b)=1 := by
    rw [←hs.2.1]; exact mirrorIndex_sum hn' hi
  rw [htp,hsp,Nat.mod_add_mod,Nat.add_mod_mod]
  have he : t.cursor.val+j+(s.cursor.val+i)=(s.cursor.val+t.cursor.val)+(i+j) := by omega
  rw [he,Nat.add_mod,hij]
  rw [Nat.add_mod (s.cursor.val+t.cursor.val) 1]
  rw [Nat.mod_eq_of_lt (by omega : 1<a+b)]

/-- Reducing a sum of two residues needs at most one wrap. -/
theorem residue_sum_cases {n x y k : Nat} (hx : x<n) (hy : y<n)
    (he : (x+y)%n=k) : x+y=k ∨ x+y=k+n := by
  by_cases h : x+y<n
  · left; rwa [Nat.mod_eq_of_lt h] at he
  · right
    have hh : x+y-n<n := by omega
    rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt hh] at he
    omega

/-- A reflection preserving each of two nonempty fixed arcs has the exact
arc phase and reverses the label order in each arc. -/
theorem arc_reflection_endpoints (ha : 0<a) (hb : 0<b) (s t : TwoState a b)
    (hsA : ∀ x, (s.posA x).val=x.val) (hsB : ∀ x, (s.posB x).val=x.val)
    (he : ∀ x, (physicalPosition t x+physicalPosition s x)%(a+b)=
      (s.cursor.val+t.cursor.val+1)%(a+b)) :
    (∀ x, (t.posA x).val+x.val+1=a) ∧
    (∀ x, (t.posB x).val+x.val+1=b) ∧
    (s.cursor.val+t.cursor.val+2)%(a+b)=a := by
  let k := (s.cursor.val+t.cursor.val+1)%(a+b)
  have hk : k<a := by
    have h0 := he (Sum.inl ⟨0,ha⟩)
    simp only [physicalPosition,hsA,Nat.add_zero] at h0
    rw [Nat.mod_eq_of_lt (by have := (t.posA ⟨0,ha⟩).isLt; omega)] at h0
    have := (t.posA ⟨0,ha⟩).isLt
    dsimp [k]; omega
  have hkedge : k+1=a := by
    by_contra hh
    have hsmall : k+1<a := by omega
    have hf := he (Sum.inl ⟨k+1,hsmall⟩)
    simp only [physicalPosition,hsA] at hf
    have hx := (t.posA ⟨k+1,hsmall⟩).isLt
    have hs := residue_sum_cases (n := a+b) (by omega) (by omega) hf
    change _=k ∨ _=k+(a+b) at hs
    omega
  have hp : (s.cursor.val+t.cursor.val+2)%(a+b)=a := by
    have heq : s.cursor.val+t.cursor.val+2=(s.cursor.val+t.cursor.val+1)+1 := by omega
    rw [heq,←Nat.mod_add_mod]
    change (k+1)%(a+b)=a
    rw [hkedge,Nat.mod_eq_of_lt (by omega : a<a+b)]
  refine ⟨?_,?_,hp⟩
  · intro x
    have hx := (t.posA x).isLt
    have hi := x.isLt
    have hf := he (Sum.inl x)
    simp only [physicalPosition,hsA] at hf
    have hh := residue_sum_cases (n := a+b) (by omega) (by omega) hf
    change _=k ∨ _=k+(a+b) at hh
    omega
  · intro x
    have hx := (t.posB x).isLt
    have hi := x.isLt
    have hf := he (Sum.inr x)
    simp only [physicalPosition,hsB] at hf
    have hh := residue_sum_cases (n := a+b) (by omega) (by omega) hf
    change _=k ∨ _=k+(a+b) at hh
    omega

/-- Nondegenerate native lower bound once the initial indexed arc
presentation is supplied. Trace, final reversals, phase and price are derived. -/
theorem native_indexed_lower (ha : 2≤a) (hb : 2≤b) {s : TwoState a b}
    {xs : List (Label a b)} (hs : Represents s xs)
    (hall : ∀ x, x∈xs)
    (hsA : ∀ x, (s.posA x).val=x.val) (hsB : ∀ x, (s.posB x).val=x.val)
    (w : List Op) (hm : MonoTrace color w xs)
    (hend : run w xs=LRX.Cycle11WordSymmetry.reflect xs) :
    (a+b)*(a+b-1)/2≤w.length := by
  obtain ⟨t,htrace,ht⟩ := native_trace_lift (by omega) (by omega) hs w hm
  rw [hend] at ht
  have he := reflected_position_sum (by omega) hs ht hall
  obtain ⟨htA,htB,hphase⟩ := arc_reflection_endpoints (by omega) (by omega) s t hsA hsB he
  exact LRX.LowerBoundSwapBudget.physical_two_block_total_lower ha hb htrace hsA hsB htA htB hphase

/-- Cyclic adjacency is exact adjacency of list indices modulo its length. -/
theorem pair_index {α : Type*} {xs : List α} {x y : α}
    (h : LRX.Cycle11PairEncounter.Pair x y xs) :
    ∃ (i : Nat) (hi : i<xs.length), xs[i]=x ∧
      xs[(i+1)%xs.length]'(Nat.mod_lt _ (by omega))=y := by
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp h
  have hl : (left xs).length=xs.length := (step_perm .L xs).length_eq
  have hi' : i<xs.length := by
    simpa only [LRX.Cycle11PairEncounter.edges,List.length_zipWith,hl,min_self] using hi
  simp only [LRX.Cycle11PairEncounter.edges,List.getElem_zipWith] at he
  refine ⟨i,hi',?_,?_⟩
  · exact congrArg Prod.fst he
  · have hh := congrArg Prod.snd he
    change (left xs)[i]'(by omega)=y at hh
    simp only [left_rotate,List.getElem_rotate] at hh
    exact hh

theorem pair_indices {α : Type*} {xs : List α} (hs : xs.Nodup)
    {i j : Nat} (hi : i<xs.length) (hj : j<xs.length)
    (h : LRX.Cycle11PairEncounter.Pair xs[i] xs[j] xs) :
    (i+1)%xs.length=j := by
  obtain ⟨k,hk,hki,hkj⟩ := pair_index h
  have he : k=i := hs.getElem_inj.mp hki
  subst k
  exact hs.getElem_inj.mp hkj

/-- Two retained same-color labels separated on both sides cannot be cyclic
neighbors. Used to extract actual arcs from the previous pairwise criterion. -/
theorem separated_by_nonempty {α : Type*} (x y : α) (p q : List α)
    (hs : (x::p++y::q).Nodup) (hp : 0<p.length) (hq : 0<q.length) :
    ¬LRX.Cycle11PairEncounter.Pair x y (x::p++y::q) ∧
    ¬LRX.Cycle11PairEncounter.Pair y x (x::p++y::q) := by
  let xs := x::p++y::q
  have h0 : 0<xs.length := by simp [xs]
  have hj : p.length+1<xs.length := by simp only [xs,List.length_cons,List.length_append]; omega
  have hx : xs[0]=x := rfl
  have hy : xs[p.length+1]=y := by
    simp [xs,List.getElem_append_right]
  constructor
  · intro h
    have h' : LRX.Cycle11PairEncounter.Pair xs[0] xs[p.length+1] xs := by
      simpa only [hx,hy] using h
    have hh := pair_indices (xs := xs) hs h0 hj h'
    have hn : 1<xs.length := by simp only [xs,List.length_cons,List.length_append]; omega
    simp only [Nat.zero_add,Nat.mod_eq_of_lt hn] at hh
    omega
  · intro h
    have h' : LRX.Cycle11PairEncounter.Pair xs[p.length+1] xs[0] xs := by
      simpa only [hx,hy] using h
    have hh := pair_indices (xs := xs) hs hj h0 h'
    have hn : p.length+1+1<xs.length := by simp only [xs,List.length_cons,List.length_append]; omega
    rw [Nat.mod_eq_of_lt hn] at hh
    omega

def Contiguous {α : Type*} [DecidableEq α] (c : α → Bool) (xs : List α) : Prop :=
  ∀ x y, x≠y → c x=c y →
    LRX.Cycle11PairEncounter.Pair x y (xs.filter (keepPair c x y)) ∨
    LRX.Cycle11PairEncounter.Pair y x (xs.filter (keepPair c x y))

theorem no_split_opponents {α : Type*} [DecidableEq α] (c : α → Bool)
    (x y : α) (p q : List α) (hs : (x::p++y::q).Nodup)
    (hc : Contiguous c (x::p++y::q)) (he : c x=c y)
    (hp : ∃ z∈p, c z≠c x) (hq : ∃ z∈q, c z≠c x) : False := by
  have hxy : x≠y := by
    have hh := (List.nodup_cons.mp hs).1
    intro h; subst y; exact hh (by simp)
  have hkx : keepPair c x y x=true := by simp [keepPair]
  have hky : keepPair c x y y=true := by simp [keepPair]
  have hfiltered := hs.filter (keepPair c x y)
  simp only [List.filter_cons,List.filter_append,hkx,hky,ite_true] at hfiltered
  have hplen : 0<(p.filter (keepPair c x y)).length := by
    obtain ⟨z,hz,he⟩ := hp
    exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hz,by simp [keepPair,he]⟩)
  have hqlen : 0<(q.filter (keepPair c x y)).length := by
    obtain ⟨z,hz,he⟩ := hq
    exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hz,by simp [keepPair,he]⟩)
  have hsep := separated_by_nonempty x y _ _ hfiltered hplen hqlen
  have hpair := hc x y hxy he
  simp only [List.filter_cons,List.filter_append,hkx,hky,ite_true] at hpair
  exact hpair.elim hsep.1 hsep.2

/-- Linear normal form relative to the color of the first label. -/
def ThreeRuns {α : Type*} (c : α → Bool) (z : α) (xs : List α) : Prop :=
  ∃ p q r, xs=p++q++r ∧
    (∀ x∈p,c x=c z) ∧ (∀ x∈q,c x≠c z) ∧ (∀ x∈r,c x=c z)

def NoReturn {α : Type*} (c : α → Bool) (z : α) (xs : List α) : Prop :=
  ∀ p x q, xs=p++x::q → c x=c z →
    (∃ y∈p,c y≠c z) → ∀ y∈q,c y=c z

theorem noReturn_threeRuns {α : Type*} (c : α → Bool) (z : α) (xs : List α)
    (h : NoReturn c z xs) : ThreeRuns c z xs := by
  induction xs with
  | nil => exact ⟨[],[],[],rfl,by simp,by simp,by simp⟩
  | cons x xs ih =>
    have ht : NoReturn c z xs := by
      intro p y q he hy hp
      apply h (x::p) y q (by simp [he]) hy
      obtain ⟨v,hv,hc⟩ := hp
      exact ⟨v,by simp [hv],hc⟩
    obtain ⟨p,q,r,he,hp,hq,hr⟩ := ih ht
    by_cases hx : c x=c z
    · exact ⟨x::p,q,r,by simp [he],by simpa only [List.mem_cons,forall_eq_or_imp] using And.intro hx hp,hq,hr⟩
    · by_cases hempty : p=[]
      · subst p
        exact ⟨[],x::q,r,by simpa using congrArg (List.cons x) he,
          by simp,by simpa only [List.mem_cons,forall_eq_or_imp] using And.intro hx hq,hr⟩
      · obtain ⟨y,p',rfl⟩ := List.exists_cons_of_ne_nil hempty
        have hall := h [x] y (p'++q++r) (by simp [he,List.append_assoc])
          (hp y (by simp)) ⟨x,by simp,hx⟩
        exact ⟨[],[x],y::p'++q++r,by simp [he,List.append_assoc],by simp,
          by simp [hx],by simpa using And.intro (hp y (by simp)) hall⟩

theorem contiguous_threeRuns {α : Type*} [DecidableEq α] (c : α → Bool)
    (z : α) (xs : List α) (hs : (z::xs).Nodup) (hc : Contiguous c (z::xs)) :
    ThreeRuns c z (z::xs) := by
  have hn : NoReturn c z xs := by
    intro p x q he hx hp y hy
    by_contra hne
    have hs' : (z::p++x::q).Nodup := by simpa [he] using hs
    have hc' : Contiguous c (z::p++x::q) := by simpa [he] using hc
    exact no_split_opponents c z x p q hs' hc' hx.symm hp ⟨y,hy,hne⟩
  obtain ⟨p,q,r,he,hp,hq,hr⟩ := noReturn_threeRuns c z xs hn
  exact ⟨z::p,q,r,by simp [he],by simpa only [List.mem_cons,forall_eq_or_imp] using And.intro (show c z=c z from rfl) hp,hq,hr⟩

theorem contiguous_two_arcs {α : Type*} [DecidableEq α] (c : α → Bool)
    (z : α) (xs : List α) (hs : (z::xs).Nodup) (hc : Contiguous c (z::xs)) :
    ∃ (p q : List α) (k : Nat), (z::xs).rotate k=p++q ∧
      (∀ x∈p,c x=c z) ∧ (∀ x∈q,c x≠c z) := by
  obtain ⟨p,q,r,he,hp,hq,hr⟩ := contiguous_threeRuns c z xs hs hc
  refine ⟨r++p,q,(p++q).length,?_,?_,hq⟩
  · rw [he,List.rotate_append_length_eq]
    simp only [List.append_assoc]
  · intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact hr x hx
    · exact hp x hx

def arcEquiv {α : Type*} [DecidableEq α] (p q : List α)
    (hs : (p++q).Nodup) (hall : ∀ x, x∈p++q) : Label p.length q.length ≃ α :=
  finSumFinEquiv.trans ((finCongr (show (p++q).length=p.length+q.length from List.length_append).symm).trans
    (List.Nodup.getEquivOfForallMemList (p++q) hs hall))

theorem arcEquiv_inl {α : Type*} [DecidableEq α] (p q : List α)
    (hs : (p++q).Nodup) (hall : ∀ x, x∈p++q) (x : Fin p.length) :
    arcEquiv p q hs hall (.inl x)=p[x.val] := by
  change (p++q)[x.val]=p[x.val]
  exact List.getElem_append_left x.isLt

theorem arcEquiv_inr {α : Type*} [DecidableEq α] (p q : List α)
    (hs : (p++q).Nodup) (hall : ∀ x, x∈p++q) (x : Fin q.length) :
    arcEquiv p q hs hall (.inr x)=q[x.val] := by
  change (p++q)[p.length+x.val]=q[x.val]
  rw [List.getElem_append_right (by omega)]
  simp

def initial (a b c : Nat) (hn : 0<a+b) : TwoState a b where
  posA := Equiv.refl _
  posB := Equiv.refl _
  cursor := ⟨c%(a+b),Nat.mod_lt _ hn⟩
  winding := 0

theorem initial_position (a b c : Nat) (hn : 0<a+b) (x : Label a b) :
    physicalPosition (initial a b c hn) x=(finSumFinEquiv x).val := by
  cases x <;> rfl

theorem represents_arc_root {α : Type*} [DecidableEq α] (p q : List α)
    (hs : (p++q).Nodup) (hall : ∀ x, x∈p++q) (hn : 0<p.length+q.length) :
    Represents (initial p.length q.length 0 hn) ((p++q).map (arcEquiv p q hs hall).symm) := by
  let e := arcEquiv p q hs hall
  refine ⟨hs.map e.symm.injective,by simp,?_⟩
  intro i hi
  have hi' : i<(p++q).length := by simpa using hi
  have hi'' : i<p.length+q.length := by simpa using hi'
  let j : Fin (p.length+q.length) := ⟨i,hi''⟩
  have he : e (finSumFinEquiv.symm j)=(p++q)[i] := by
    change (List.Nodup.getEquivOfForallMemList (p++q) hs hall)
      ((finCongr (show (p++q).length=p.length+q.length from List.length_append).symm) (finSumFinEquiv (finSumFinEquiv.symm j)))=_
    rw [Equiv.apply_symm_apply]
    rfl
  have hei : e.symm ((p++q)[i])=finSumFinEquiv.symm j := by
    rw [←he,Equiv.symm_apply_apply]
  simp only [List.getElem_map]
  change physicalPosition (initial p.length q.length 0 hn) (e.symm ((p++q)[i]))=_
  rw [hei,initial_position,Equiv.apply_symm_apply]
  change i=(0%(p.length+q.length)+i)%(p.length+q.length)
  simp [Nat.mod_eq_of_lt hi'']

theorem represents_arc_rotation {α : Type*} [DecidableEq α] (xs p q : List α)
    (k : Nat) (he : xs.rotate k=p++q) (hs : xs.Nodup) (hall : ∀ x,x∈xs)
    (hn : 0<xs.length) :
    ∃ (e : Label p.length q.length ≃ α) (s : TwoState p.length q.length),
      Represents s (xs.map e.symm) ∧
      (∀ x,(s.posA x).val=x.val) ∧ (∀ x,(s.posB x).val=x.val) ∧
      (∀ x : Fin p.length, e (.inl x)=p[x.val]) ∧
      (∀ x : Fin q.length, e (.inr x)=q[x.val]) := by
  have hnd : (p++q).Nodup := he ▸ (List.nodup_rotate.mpr hs)
  have hall' : ∀ x,x∈p++q := by intro x; rw [←he]; exact List.mem_rotate.mpr (hall x)
  have hlen : xs.length=p.length+q.length := by
    have hh := congrArg List.length he
    simpa using hh
  have hn' : 0<p.length+q.length := by omega
  let e := arcEquiv p q hnd hall'
  let d := (p++q).length-k%(p++q).length
  let s := initial p.length q.length d hn'
  refine ⟨e,s,?_,fun _ => rfl,fun _ => rfl,arcEquiv_inl p q hnd hall',arcEquiv_inr p q hnd hall'⟩
  have hr := represents_arc_root p q hnd hall' hn'
  have hh := represents_rotate (t := s) hr d
    (fun x => by cases x <;> rfl) (by simp [s,initial])
  have he' := List.rotate_eq_iff.mp he
  rw [he',List.map_rotate]
  exact hh

theorem headPair_map {α β : Type*} (f : α → β) (x y : α) (xs : List α)
    (h : HeadPair x y xs) : HeadPair (f x) (f y) (xs.map f) := by
  rcases h with ⟨tail,rfl⟩|⟨tail,rfl⟩
  · exact Or.inl ⟨tail.map f,rfl⟩
  · exact Or.inr ⟨tail.map f,rfl⟩

theorem mono_equiv {α : Type*} [DecidableEq α] (c : α → Bool)
    (e : Label a b ≃ α) (xs : List α) (w : List Op)
    (hm : MonoTrace c w xs)
    (he : ∀ x y, c (e x)=c (e y) → color x=color y) :
    MonoTrace color w (xs.map e.symm) := by
  intro u v x y hw hp
  have hh := headPair_map e x y (run u (xs.map e.symm)) hp
  rw [←run_map,List.map_map] at hh
  have hi : (⇑e ∘ ⇑e.symm)=id := by funext x; exact e.apply_symm_apply x
  rw [hi,List.map_id] at hh
  exact he x y (hm u v (e x) (e y) hw hh)

theorem arc_color_compatible {α : Type*} [DecidableEq α] (c : α → Bool)
    (z : α) (p q : List α) (e : Label p.length q.length ≃ α)
    (hep : ∀ x : Fin p.length,e (.inl x)=p[x.val])
    (heq : ∀ x : Fin q.length,e (.inr x)=q[x.val])
    (hp : ∀ x∈p,c x=c z) (hq : ∀ x∈q,c x≠c z) :
    ∀ x y, c (e x)=c (e y) → color x=color y := by
  intro x y h
  cases x with
  | inl x => cases y with
    | inl y => rfl
    | inr y =>
      rw [hep,heq] at h
      exact False.elim ((hq _ (List.getElem_mem _)) (h.symm.trans (hp _ (List.getElem_mem _))))
  | inr x => cases y with
    | inl y =>
      rw [heq,hep] at h
      exact False.elim ((hq _ (List.getElem_mem _)) (h.trans (hp _ (List.getElem_mem _))))
    | inr y => rfl

theorem arc_color_iff {α : Type*} [DecidableEq α] (c : α → Bool)
    (z : α) (p q : List α) (e : Label p.length q.length ≃ α)
    (hep : ∀ x : Fin p.length,e (.inl x)=p[x.val])
    (heq : ∀ x : Fin q.length,e (.inr x)=q[x.val])
    (hp : ∀ x∈p,c x=c z) (hq : ∀ x∈q,c x≠c z) :
    ∀ x y, c (e x)=c (e y) ↔ color x=color y := by
  intro x y
  refine ⟨arc_color_compatible c z p q e hep heq hp hq x y,?_⟩
  intro h
  cases x with
  | inl x => cases y with
    | inl y =>
      rw [hep,hep]
      exact (hp _ (List.getElem_mem _)).trans (hp _ (List.getElem_mem _)).symm
    | inr y => simp [color] at h
  | inr x => cases y with
    | inl y => simp [color] at h
    | inr y =>
      rw [heq,heq]
      have hx := hq q[x.val] (List.getElem_mem x.isLt)
      have hy := hq q[y.val] (List.getElem_mem y.isLt)
      cases hz : c z <;> cases hx' : c q[x.val] <;> cases hy' : c q[y.val] <;> simp_all

theorem reflect_map {α β : Type*} (f : α → β) (xs : List α) :
    LRX.Cycle11WordSymmetry.reflect (xs.map f)=(LRX.Cycle11WordSymmetry.reflect xs).map f := by
  cases xs with
  | nil => rfl
  | cons x xs => cases xs <;> simp [LRX.Cycle11WordSymmetry.reflect,List.map_reverse]

/-- The structural theorem now produces the indexed initial state and the
native monochromatic word. It imposes no PhysicalTrace hypothesis. -/
theorem shortest_indexed_presentation {α : Type*} [DecidableEq α]
    (w : List Op) (xs : List α) (z : α) (hs : xs.Nodup) (hall : ∀ x,x∈xs)
    (hmin : Shortest w xs) (hend : run w xs=LRX.Cycle11WordSymmetry.reflect xs) :
    ∃ (a b : Nat) (e : Label a b ≃ α) (s : TwoState a b),
      a+b=xs.length ∧ Represents s (xs.map e.symm) ∧
      (∀ x,(s.posA x).val=x.val) ∧ (∀ x,(s.posB x).val=x.val) ∧
      (∀ x y : Label a b,x≠y → LRX.LowerBoundSwapCount.swapCount (e x) (e y) w xs=
        if color x=color y then 1 else 0) ∧
      MonoTrace color w (xs.map e.symm) ∧
      run w (xs.map e.symm)=LRX.Cycle11WordSymmetry.reflect (xs.map e.symm) := by
  have href : run w xs=run [.R,.R] xs.reverse := by
    rw [hend,LRX.Cycle11WordSymmetry.reflect_as_reverse]; rfl
  have hrot : LRX.LowerBoundPairParity.Rotations [.R,.R] := by
    simp [LRX.LowerBoundPairParity.Rotations]
  obtain ⟨c,hcount,hcontig⟩ := shortest_reflection_contiguity w [.R,.R] xs z hs hall hmin hrot href
  have hm := counts_mono c w xs hs hcount
  have hn : 0<xs.length := List.length_pos_of_mem (hall z)
  obtain ⟨y,tail,hxs⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hn)
  obtain ⟨p,q,k,hpq,hp,hq⟩ := contiguous_two_arcs c y tail (hxs ▸ hs) (hxs ▸ hcontig)
  rw [←hxs] at hpq
  obtain ⟨e,s,hrep,hsA,hsB,hep,heq⟩ := represents_arc_rotation xs p q k hpq hs hall hn
  refine ⟨p.length,q.length,e,s,?_,hrep,hsA,hsB,?_,?_,?_⟩
  · have hlen := congrArg List.length hpq
    simpa using hlen.symm
  · intro x1 x2 hxy
    have hh := hcount (e x1) (e x2) (fun hh => hxy (e.injective hh))
    simp only [arc_color_iff c y p q e hep heq hp hq] at hh
    exact hh
  · exact mono_equiv c e xs w hm (arc_color_compatible c y p q e hep heq hp hq)
  · rw [run_map,hend,reflect_map]

theorem shortest_representative {α : Type*} (w : List Op) (xs : List α) :
    ∃ v, Shortest v xs ∧ run v xs=run w xs ∧ v.length≤w.length := by
  classical
  have hex : ∃ n : Nat, ∃ v : List Op, v.length=n ∧ run v xs=run w xs :=
    ⟨w.length,w,rfl,rfl⟩
  obtain ⟨v,hv,he⟩ := Nat.find_spec hex
  have hm : Shortest v xs := by
    intro u hu
    rw [hv]
    exact Nat.find_min' hex ⟨u,rfl,hu.trans he⟩
  exact ⟨v,hm,he,hm w he.symm⟩

/-- Complete structural-to-physical reduction of an arbitrary native
reflection word. Degenerate class sizes remain explicit branches.
For positive classes the actual trace and all endpoint conditions are outputs. -/
theorem native_physical_reduction {α : Type*} [DecidableEq α]
    (w : List Op) (xs : List α) (z : α) (hs : xs.Nodup) (hall : ∀ x,x∈xs)
    (hend : run w xs=LRX.Cycle11WordSymmetry.reflect xs) :
    ∃ (v : List Op) (a b : Nat) (e : Label a b ≃ α) (s : TwoState a b),
      v.length≤w.length ∧ Shortest v xs ∧ run v xs=run w xs ∧
      a+b=xs.length ∧ Represents s (xs.map e.symm) ∧
      (∀ x,(s.posA x).val=x.val) ∧ (∀ x,(s.posB x).val=x.val) ∧
      (∀ x y : Label a b,x≠y → LRX.LowerBoundSwapCount.swapCount (e x) (e y) v xs=
        if color x=color y then 1 else 0) ∧
      MonoTrace color v (xs.map e.symm) ∧
      run v (xs.map e.symm)=LRX.Cycle11WordSymmetry.reflect (xs.map e.symm) ∧
      (0<a → 0<b → ∃ t, PhysicalTrace s v t ∧ Represents t (run v (xs.map e.symm)) ∧
        (∀ x,(t.posA x).val+x.val+1=a) ∧
        (∀ x,(t.posB x).val+x.val+1=b) ∧
        (s.cursor.val+t.cursor.val+2)%(a+b)=a) ∧
      (2≤a → 2≤b → xs.length*(xs.length-1)/2≤w.length) := by
  obtain ⟨v,hmin,hend',hlen⟩ := shortest_representative w xs
  obtain ⟨a,b,e,s,hn,hrep,hsA,hsB,hcount,hm,he⟩ :=
    shortest_indexed_presentation v xs z hs hall hmin (hend'.trans hend)
  have hall' : ∀ x : Label a b,x∈xs.map e.symm := by
    intro x
    exact List.mem_map.mpr ⟨e x,hall (e x),e.symm_apply_apply x⟩
  refine ⟨v,a,b,e,s,hlen,hmin,hend',hn,hrep,hsA,hsB,hcount,hm,he,?_,?_⟩
  · intro ha hb
    obtain ⟨t,htrace,ht⟩ := native_trace_lift ha hb hrep v hm
    have href : Represents t (LRX.Cycle11WordSymmetry.reflect (xs.map e.symm)) := he ▸ ht
    have hsum := reflected_position_sum (by omega) hrep href hall'
    obtain ⟨htA,htB,hphase⟩ := arc_reflection_endpoints ha hb s t hsA hsB hsum
    exact ⟨t,htrace,ht,htA,htB,hphase⟩
  · intro ha hb
    have hlow := native_indexed_lower ha hb hrep hall' hsA hsB v hm he
    rw [hn] at hlow
    exact hlow.trans hlen

#print axioms shortest_representative
#print axioms native_physical_reduction
#print axioms shortest_indexed_presentation
#print axioms represents_arc_rotation
#print axioms contiguous_two_arcs
#print axioms reflected_position_sum
#print axioms arc_reflection_endpoints
#print axioms native_indexed_lower
#print axioms represents_next
#print axioms represents_prev
#print axioms exchange_physical
#print axioms native_trace_lift
end LRX.LowerBoundNativeTrace
