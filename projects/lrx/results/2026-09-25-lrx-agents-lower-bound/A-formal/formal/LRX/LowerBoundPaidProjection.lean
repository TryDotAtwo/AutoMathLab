import LRX.LowerBoundFoldedTransport

/-! Exact projection of paid physical cursor moves onto two fixed arcs.
The state stores the actual within-arc label positions as permutations.
This module is separate from the earlier failed independent-distance relaxation. -/
namespace LRX.LowerBoundPaidProjection
open LRX.LowerBoundFoldedTransport LRX.BlockExchange

structure TwoState (a b : Nat) where
  posA : Equiv.Perm (Fin a)
  posB : Equiv.Perm (Fin b)
  cursor : Fin (a+b)
  winding : Int

variable {a b : Nat}

def projectA (ha : 0<a) (s : TwoState a b) : State a where
  pos := s.posA
  cursor := ⟨min s.cursor.val (a-1),by have := s.cursor.isLt; omega⟩
  winding := s.winding

def projectB (hb : 0<b) (s : TwoState a b) : State b where
  pos := s.posB
  cursor := ⟨if s.cursor.val<a then b-1 else s.cursor.val-a,by
    have := s.cursor.isLt
    split_ifs <;> omega⟩
  winding := s.winding - (if s.cursor.val<a then 1 else 0)

def Left {a b : Nat} (s t : TwoState a b) : Prop :=
  t.posA=s.posA ∧ t.posB=s.posB ∧
  ((t.cursor.val=s.cursor.val+1 ∧ t.winding=s.winding) ∨
   (s.cursor.val+1=a+b ∧ t.cursor.val=0 ∧ t.winding=s.winding+1))

theorem state_ext {j : Nat} {s t : State j}
    (hp : s.pos=t.pos) (hc : s.cursor.val=t.cursor.val) (hh : s.winding=t.winding) : s=t := by
  cases s; cases t
  simp_all only [Fin.val_inj]

/-- Each actual L belongs to exactly one local rotation budget; the other
projection is literally unchanged, including its winding. -/
theorem left_partition (ha : 0<a) (hb : 0<b) {s t : TwoState a b}
    (h : Left s t) :
    (LRX.LowerBoundFoldedTransport.Left (projectA ha s) (projectA ha t) ∧
      projectB hb t=projectB hb s) ∨
    (projectA ha t=projectA ha s ∧
      LRX.LowerBoundFoldedTransport.Left (projectB hb s) (projectB hb t)) := by
  obtain ⟨hpA,hpB,hi|hw⟩ := h
  · obtain ⟨hc,hh⟩ := hi
    by_cases hin : s.cursor.val+1<a
    · left
      constructor
      · constructor
        · exact hpA
        · left
          constructor
          · change min t.cursor.val (a-1)=min s.cursor.val (a-1)+1
            omega
          · exact hh
      · apply state_ext
        · exact hpB
        · change (if t.cursor.val<a then b-1 else t.cursor.val-a)=
            (if s.cursor.val<a then b-1 else s.cursor.val-a)
          have hs : s.cursor.val<a := by omega
          have ht : t.cursor.val<a := by omega
          simp [hs,ht]
        · change t.winding-(if t.cursor.val<a then 1 else 0)=
            s.winding-(if s.cursor.val<a then 1 else 0)
          have hs : s.cursor.val<a := by omega
          have ht : t.cursor.val<a := by omega
          simp [hs,ht,hh]
    · right
      constructor
      · apply state_ext hpA ?_ hh
        change min t.cursor.val (a-1)=min s.cursor.val (a-1)
        omega
      · constructor
        · exact hpB
        · by_cases he : s.cursor.val+1=a
          · right
            have hs : s.cursor.val<a := by omega
            have ht : ¬t.cursor.val<a := by omega
            change ((if s.cursor.val<a then b-1 else s.cursor.val-a)+1=b) ∧
              (if t.cursor.val<a then b-1 else t.cursor.val-a)=0 ∧
              t.winding-(if t.cursor.val<a then 1 else 0)=
                s.winding-(if s.cursor.val<a then 1 else 0)+1
            simp only [hs,ht,ite_true,ite_false,hh]
            omega
          · left
            have hs : ¬s.cursor.val<a := by omega
            have ht : ¬t.cursor.val<a := by omega
            change (if t.cursor.val<a then b-1 else t.cursor.val-a)=
              (if s.cursor.val<a then b-1 else s.cursor.val-a)+1 ∧
              t.winding-(if t.cursor.val<a then 1 else 0)=
                s.winding-(if s.cursor.val<a then 1 else 0)
            simp only [hs,ht,ite_false,hh]
            constructor
            · omega
            · trivial
  · obtain ⟨hj,hc,hh⟩ := hw
    left
    constructor
    · constructor
      · exact hpA
      · right
        change min s.cursor.val (a-1)+1=a ∧ min t.cursor.val (a-1)=0 ∧
          t.winding=s.winding+1
        omega
    · apply state_ext
      · exact hpB
      · change (if t.cursor.val<a then b-1 else t.cursor.val-a)=
          (if s.cursor.val<a then b-1 else s.cursor.val-a)
        have hs : ¬s.cursor.val<a := by omega
        have ht : t.cursor.val<a := by omega
        simp only [hs,ht,ite_true,ite_false]
        omega
      · change t.winding-(if t.cursor.val<a then 1 else 0)=
          s.winding-(if s.cursor.val<a then 1 else 0)
        have hs : ¬s.cursor.val<a := by omega
        have ht : t.cursor.val<a := by omega
        simp [hs,ht,hh]

/-- Concrete physical L/R and within-arc adjacent X. The untouched arc,
cursor, and winding at X are explicitly unchanged. -/
inductive Step (ha : 0<a) (hb : 0<b) : TwoState a b → Op → TwoState a b → Prop where
  | left {s t} : Left s t → Step ha hb s .L t
  | right {s t} : Left t s → Step ha hb s .R t
  | exchangeA {s t} : Exchange (projectA ha s) (projectA ha t) →
      t.cursor=s.cursor → t.winding=s.winding → t.posB=s.posB → Step ha hb s .X t
  | exchangeB {s t} : Exchange (projectB hb s) (projectB hb t) →
      t.cursor=s.cursor → t.winding=s.winding → t.posA=s.posA → Step ha hb s .X t

inductive Trace (ha : 0<a) (hb : 0<b) : TwoState a b → List Op → TwoState a b → Prop where
  | nil (s) : Trace ha hb s [] s
  | cons {s m t op w} : Step ha hb s op m → Trace ha hb m w t → Trace ha hb s (op::w) t

theorem local_trace_append {j : Nat} {s m t : State j} {u v : List Op}
    (hu : LRX.LowerBoundFoldedTransport.Trace s u m)
    (hv : LRX.LowerBoundFoldedTransport.Trace m v t) :
    LRX.LowerBoundFoldedTransport.Trace s (u++v) t := by
  induction hu with
  | nil => exact hv
  | cons h _ ih => exact .cons h (ih hv)

theorem local_single {j : Nat} {s t : State j} {op : Op}
    (h : LRX.LowerBoundFoldedTransport.Step s op t) :
    LRX.LowerBoundFoldedTransport.Trace s [op] t := .cons h (.nil t)

theorem step_projection (ha : 0<a) (hb : 0<b) {s t : TwoState a b} {op : Op}
    (h : Step ha hb s op t) :
    ∃ u v : List Op,
      LRX.LowerBoundFoldedTransport.Trace (projectA ha s) u (projectA ha t) ∧
      LRX.LowerBoundFoldedTransport.Trace (projectB hb s) v (projectB hb t) ∧
      rotations u+rotations v=price op := by
  cases h with
  | left h =>
    rcases left_partition ha hb h with ⟨hA,hB⟩ | ⟨hA,hB⟩
    · refine ⟨[.L],[],local_single (.left hA),?_,by simp [rotations,price]⟩
      rw [hB]
      exact .nil _
    · refine ⟨[],[.L],?_,local_single (.left hB),by simp [rotations,price]⟩
      rw [hA]
      exact .nil _
  | right h =>
    rcases left_partition ha hb h with ⟨hA,hB⟩ | ⟨hA,hB⟩
    · refine ⟨[.R],[],local_single (.right hA),?_,by simp [rotations,price]⟩
      rw [hB]
      exact .nil _
    · refine ⟨[],[.R],?_,local_single (.right hB),by simp [rotations,price]⟩
      rw [hA]
      exact .nil _
  | exchangeA h hc hh hp =>
    have he : projectB hb t=projectB hb s := by
      apply state_ext hp <;> simp [projectB,hc,hh]
    refine ⟨[.X],[],local_single (.exchange h),?_,by simp [rotations,price]⟩
    rw [he]
    exact .nil _
  | exchangeB h hc hh hp =>
    have he : projectA ha t=projectA ha s := by
      apply state_ext hp <;> simp [projectA,hc,hh]
    refine ⟨[],[.X],?_,local_single (.exchange h),by simp [rotations,price]⟩
    rw [he]
    exact .nil _

/-- Exact paid projection of every actual two-arc trace. No independent
minimizer is substituted; both local traces come from this same word. -/
theorem trace_projection (ha : 0<a) (hb : 0<b) {s t : TwoState a b} {w : List Op}
    (h : Trace ha hb s w t) :
    ∃ u v : List Op,
      LRX.LowerBoundFoldedTransport.Trace (projectA ha s) u (projectA ha t) ∧
      LRX.LowerBoundFoldedTransport.Trace (projectB hb s) v (projectB hb t) ∧
      rotations u+rotations v=rotations w := by
  induction h with
  | nil s => exact ⟨[],[],.nil _,.nil _,rfl⟩
  | @cons s m t op w hs ht ih =>
    obtain ⟨u1,v1,hA1,hB1,hp1⟩ := step_projection ha hb hs
    obtain ⟨u2,v2,hA2,hB2,hp2⟩ := ih
    refine ⟨u1++u2,v1++v2,local_trace_append hA1 hA2,local_trace_append hB1 hB2,?_⟩
    simp only [rotations_append,rotations]
    omega

def ExternalVisit {j : Nat} (s : State j) (w : List Op) (t : State j) : Prop :=
  ∃ (m : State j) (u v : List Op), w=u++v ∧
    LRX.LowerBoundFoldedTransport.Trace s u m ∧
    LRX.LowerBoundFoldedTransport.Trace m v t ∧ m.cursor.val+1=j

theorem external_at_start {j : Nat} {s t : State j} {w : List Op}
    (h : LRX.LowerBoundFoldedTransport.Trace s w t) (hc : s.cursor.val+1=j) :
    ExternalVisit s w t := ⟨s,[],w,rfl,.nil s,h,hc⟩

theorem external_after_prefix {j : Nat} {s m t : State j} {u v : List Op}
    (hu : LRX.LowerBoundFoldedTransport.Trace s u m) (hv : ExternalVisit m v t) :
    ExternalVisit s (u++v) t := by
  obtain ⟨z,v1,v2,he,h1,h2,hc⟩ := hv
  exact ⟨z,u++v1,v2,by simp [he,List.append_assoc],local_trace_append hu h1,h2,hc⟩

theorem internalA_preservesB (ha : 0<a) (hb : 0<b) {s t : TwoState a b} {op : Op}
    (h : Step ha hb s op t) (hc : ¬(projectA ha s).cursor.val+1=a) :
    t.posB=s.posB := by
  have hcin : s.cursor.val<a := by
    change ¬min s.cursor.val (a-1)+1=a at hc
    omega
  cases h with
  | left h => exact h.2.1
  | right h => exact h.2.1.symm
  | exchangeA _ _ _ hp => exact hp
  | exchangeB h _ _ _ =>
    have hx := h.1
    change (if s.cursor.val<a then b-1 else s.cursor.val-a)+1<b at hx
    simp only [hcin,ite_true] at hx
    omega

theorem internalB_preservesA (ha : 0<a) (hb : 0<b) {s t : TwoState a b} {op : Op}
    (h : Step ha hb s op t) (hc : ¬(projectB hb s).cursor.val+1=b) :
    t.posA=s.posA := by
  have hcin : a≤s.cursor.val := by
    change ¬(if s.cursor.val<a then b-1 else s.cursor.val-a)+1=b at hc
    by_contra hn
    have hs : s.cursor.val<a := by omega
    simp only [hs,ite_true] at hc
    omega
  cases h with
  | left h => exact h.1
  | right h => exact h.1.symm
  | exchangeB _ _ _ hp => exact hp
  | exchangeA h _ _ _ =>
    have hx := h.1
    change min s.cursor.val (a-1)+1<a at hx
    omega

/-- Both necessary visits are retained in the SAME pair of projected words
whose rotation counts add to the actual original count. -/
theorem trace_projection_with_visits (ha : 0<a) (hb : 0<b)
    {s t : TwoState a b} {w : List Op} (h : Trace ha hb s w t) :
    ∃ u v : List Op,
      LRX.LowerBoundFoldedTransport.Trace (projectA ha s) u (projectA ha t) ∧
      LRX.LowerBoundFoldedTransport.Trace (projectB hb s) v (projectB hb t) ∧
      rotations u+rotations v=rotations w ∧
      (t.posB≠s.posB → ExternalVisit (projectA ha s) u (projectA ha t)) ∧
      (t.posA≠s.posA → ExternalVisit (projectB hb s) v (projectB hb t)) := by
  induction h with
  | nil s => exact ⟨[],[],.nil _,.nil _,rfl,by simp,by simp⟩
  | @cons s m t op w hs ht ih =>
    obtain ⟨u1,v1,hA1,hB1,hp1⟩ := step_projection ha hb hs
    obtain ⟨u2,v2,hA2,hB2,hp2,hvA,hvB⟩ := ih
    have hAt := local_trace_append hA1 hA2
    have hBt := local_trace_append hB1 hB2
    refine ⟨u1++u2,v1++v2,hAt,hBt,?_,?_,?_⟩
    · simp only [rotations_append,rotations]
      omega
    · intro hneq
      by_cases hext : (projectA ha s).cursor.val+1=a
      · exact external_at_start hAt hext
      · have he := internalA_preservesB ha hb hs hext
        apply external_after_prefix hA1
        apply hvA
        simpa only [he] using hneq
    · intro hneq
      by_cases hext : (projectB hb s).cursor.val+1=b
      · exact external_at_start hBt hext
      · have he := internalB_preservesA ha hb hs hext
        apply external_after_prefix hB1
        apply hvB
        simpa only [he] using hneq

/-- Literal normalized mirror endpoint relation (two representatives modulo n). -/
def MirrorPhase (s t : TwoState a b) : Prop :=
  s.cursor.val+t.cursor.val+2=a ∨ s.cursor.val+t.cursor.val+2=2*a+b

theorem mirrorPhase_iff_mod (ha : 0<a) (hb : 0<b) (s t : TwoState a b) :
    MirrorPhase s t ↔ (s.cursor.val+t.cursor.val+2)%(a+b)=a := by
  have hs := s.cursor.isLt
  have ht := t.cursor.isLt
  have han : a<a+b := by omega
  unfold MirrorPhase
  constructor
  · intro h
    rcases h with h | h
    · rw [h,Nat.mod_eq_of_lt han]
    · have he : 2*a+b=a+(a+b) := by omega
      rw [h,he,Nat.add_mod_right,Nat.mod_eq_of_lt han]
  · intro h
    by_cases hl : s.cursor.val+t.cursor.val+2<a+b
    · rw [Nat.mod_eq_of_lt hl] at h
      exact Or.inl h
    · have hn : a+b≤s.cursor.val+t.cursor.val+2 := by omega
      rw [Nat.mod_eq_sub_mod hn] at h
      by_cases hz : s.cursor.val+t.cursor.val+2=2*(a+b)
      · have he : s.cursor.val+t.cursor.val+2-(a+b)=a+b := by omega
        rw [he,Nat.mod_self] at h
        omega
      · have hh : s.cursor.val+t.cursor.val+2-(a+b)<a+b := by omega
        rw [Nat.mod_eq_of_lt hh] at h
        right
        omega

theorem projected_phases (ha : 0<a) (hb : 0<b) {s t : TwoState a b}
    (h : MirrorPhase s t) :
    (((projectA ha s).cursor.val+1=a ∧ (projectA ha t).cursor.val+1=a) ∨
      (projectA ha s).cursor.val+(projectA ha t).cursor.val+2=a) ∧
    (((projectB hb s).cursor.val+1=b ∧ (projectB hb t).cursor.val+1=b) ∨
      (projectB hb s).cursor.val+(projectB hb t).cursor.val+2=b) := by
  have hs := s.cursor.isLt
  have ht := t.cursor.isLt
  unfold MirrorPhase at h
  constructor
  · change ((min s.cursor.val (a-1)+1=a ∧ min t.cursor.val (a-1)+1=a) ∨
      min s.cursor.val (a-1)+min t.cursor.val (a-1)+2=a)
    omega
  · change (((if s.cursor.val<a then b-1 else s.cursor.val-a)+1=b ∧
        (if t.cursor.val<a then b-1 else t.cursor.val-a)+1=b) ∨
      (if s.cursor.val<a then b-1 else s.cursor.val-a)+
        (if t.cursor.val<a then b-1 else t.cursor.val-a)+2=b)
    split_ifs <;> omega

theorem reversal_nontrivial {j : Nat} (hj : 2≤j) (p q : Equiv.Perm (Fin j))
    (hp : ∀ x, (p x).val=x.val) (hq : ∀ x, (q x).val+x.val+1=j) : q≠p := by
  intro he
  let x : Fin j := ⟨0,by omega⟩
  have h1 := hp x
  have h2 := hq x
  rw [he] at h2
  have hx : x.val=0 := rfl
  omega

theorem two_block_unrounded (ha : 2≤a) (hb : 2≤b) {s t : TwoState a b} {w : List Op}
    (h : Trace (by omega : 0<a) (by omega : 0<b) s w t)
    (hsA : ∀ x, (s.posA x).val=x.val) (hsB : ∀ x, (s.posB x).val=x.val)
    (htA : ∀ x, (t.posA x).val+x.val+1=a)
    (htB : ∀ x, (t.posB x).val+x.val+1=b) (hp : MirrorPhase s t) :
    a*a/2+b*b/2≤rotations w := by
  have ha0 : 0<a := by omega
  have hb0 : 0<b := by omega
  obtain ⟨u,v,hA,hB,hprice,hvA,hvB⟩ := trace_projection_with_visits ha0 hb0 h
  have hneqA := reversal_nontrivial ha s.posA t.posA hsA htA
  have hneqB := reversal_nontrivial hb s.posB t.posB hsB htB
  obtain ⟨hpA,hpB⟩ := projected_phases ha0 hb0 hp
  have hboundA : a*a/2≤rotations u := by
    apply pointed_reversal_transport hA hsA htA
    rcases hpA with he | hi
    · exact Or.inl he
    · exact Or.inr ⟨hi,hvA hneqB⟩
  have hboundB : b*b/2≤rotations v := by
    apply pointed_reversal_transport hB hsB htB
    rcases hpB with he | hi
    · exact Or.inl he
    · exact Or.inr ⟨hi,hvB hneqA⟩
  omega

theorem step_cursor_parity (ha : 0<a) (hb : 0<b) {s t : TwoState a b} {op : Op}
    (h : Step ha hb s op t) (hn : (a+b)%2=0) :
    (s.cursor.val+price op)%2=t.cursor.val%2 := by
  cases h with
  | left h =>
    obtain ⟨_,_,hi|hw⟩ := h <;> simp only [price] <;> omega
  | right h =>
    obtain ⟨_,_,hi|hw⟩ := h <;> simp only [price] <;> omega
  | exchangeA _ hc _ _ => simp [price,hc]
  | exchangeB _ hc _ _ => simp [price,hc]

theorem trace_cursor_parity (ha : 0<a) (hb : 0<b) {s t : TwoState a b} {w : List Op}
    (h : Trace ha hb s w t) (hn : (a+b)%2=0) :
    (s.cursor.val+rotations w)%2=t.cursor.val%2 := by
  induction h with
  | nil s => simp [rotations]
  | @cons s m t op w hs ht ih =>
    have hstep := step_cursor_parity ha hb hs hn
    simp only [rotations]
    omega

theorem odd_blocks_odd_rotations (ha : 0<a) (hb : 0<b) {s t : TwoState a b} {w : List Op}
    (h : Trace ha hb s w t) (hp : MirrorPhase s t) (haodd : a%2=1) (hbodd : b%2=1) :
    rotations w%2=1 := by
  have hn : (a+b)%2=0 := by omega
  have hc := trace_cursor_parity ha hb h hn
  unfold MirrorPhase at hp
  omega

theorem square_mod_two (k : Nat) : (k*k)%2=k%2 := by
  rw [Nat.mul_mod]
  have hk := Nat.mod_lt k (by omega : 0<2)
  rcases (by omega : k%2=0 ∨ k%2=1) with h | h <;> simp [h]

theorem odd_square_half_even (k : Nat) (hk : k%2=1) : (k*k/2)%2=0 := by
  have hd := Nat.mod_add_div k 2
  have hs : k*k=4*((k/2)*(k/2+1))+1 := by nlinarith
  omega

theorem round_two_block_budget (a b r : Nat) (h : a*a/2+b*b/2≤r)
    (hp : a%2=1 → b%2=1 → r%2=1) : (a*a+b*b)/2≤r ∧ a*b≤r := by
  have ha := square_mod_two a
  have hb := square_mod_two b
  have hma := Nat.mod_lt a (by omega : 0<2)
  have hmb := Nat.mod_lt b (by omega : 0<2)
  have hrounded : (a*a+b*b)/2≤r := by
    by_cases hao : a%2=1
    · by_cases hbo : b%2=1
      · have hr := hp hao hbo
        have hqa := odd_square_half_even a hao
        have hqb := odd_square_half_even b hbo
        omega
      · omega
    · omega
  have hsquare : 2*a*b≤a*a+b*b := by
    have hZ : (2 : Int)*a*b≤(a : Int)*a+(b : Int)*b := by
      nlinarith [sq_nonneg ((a : Int)-(b : Int))]
    exact_mod_cast hZ
  rw [Nat.mul_assoc] at hsquare
  constructor
  · exact hrounded
  · omega

/-- General two-block rotation bound, proved for actual paid two-arc traces.
All interleavings, repeated X and windings are allowed. No hypothetical lower
bound is supplied as an assumption; only literal initial/final states and phase.
The remaining original-graph interface is the structural reduction to TwoState. -/
theorem two_block_rotation_lower (ha : 2≤a) (hb : 2≤b) {s t : TwoState a b} {w : List Op}
    (h : Trace (by omega : 0<a) (by omega : 0<b) s w t)
    (hsA : ∀ x, (s.posA x).val=x.val) (hsB : ∀ x, (s.posB x).val=x.val)
    (htA : ∀ x, (t.posA x).val+x.val+1=a)
    (htB : ∀ x, (t.posB x).val+x.val+1=b) (hp : MirrorPhase s t) :
    (a*a+b*b)/2≤rotations w ∧ a*b≤rotations w := by
  have hu := two_block_unrounded ha hb h hsA hsB htA htB hp
  apply round_two_block_budget a b (rotations w) hu
  intro haodd hbodd
  exact odd_blocks_odd_rotations (by omega) (by omega) h hp haodd hbodd

theorem two_block_rotation_lower_mod (ha : 2≤a) (hb : 2≤b)
    {s t : TwoState a b} {w : List Op}
    (h : Trace (by omega : 0<a) (by omega : 0<b) s w t)
    (hsA : ∀ x, (s.posA x).val=x.val) (hsB : ∀ x, (s.posB x).val=x.val)
    (htA : ∀ x, (t.posA x).val+x.val+1=a)
    (htB : ∀ x, (t.posB x).val+x.val+1=b)
    (hp : (s.cursor.val+t.cursor.val+2)%(a+b)=a) :
    (a*a+b*b)/2≤rotations w ∧ a*b≤rotations w := by
  exact two_block_rotation_lower ha hb h hsA hsB htA htB
    ((mirrorPhase_iff_mod (by omega) (by omega) s t).mpr hp)

/-- Position of each actual label on the full physical circle. -/
def physicalPosition (s : TwoState a b) : Sum (Fin a) (Fin b) → Nat
  | .inl x => (s.posA x).val
  | .inr x => a+(s.posB x).val

def physicalSwapPosition (c z : Nat) : Nat :=
  if z=c then c+1 else if z=c+1 then c else z

/-- Literal adjacent physical transposition, with precisely the two inter-arc
edges forbidden. This definition uses no projected coordinates. -/
def PhysicalX (s t : TwoState a b) : Prop :=
  t.cursor=s.cursor ∧ t.winding=s.winding ∧ s.cursor.val+1<a+b ∧
  s.cursor.val+1≠a ∧
  ∀ x, physicalPosition t x=physicalSwapPosition s.cursor.val (physicalPosition s x)

theorem exchangeA_physical (ha : 0<a) (hb : 0<b) {s t : TwoState a b}
    (h : Exchange (projectA ha s) (projectA ha t))
    (hc : t.cursor=s.cursor) (hh : t.winding=s.winding) (hp : t.posB=s.posB) :
    PhysicalX s t := by
  have hx := h.1
  change min s.cursor.val (a-1)+1<a at hx
  have hi : s.cursor.val+1<a := by omega
  have hmin : min s.cursor.val (a-1)=s.cursor.val := by omega
  refine ⟨hc,hh,by omega,by omega,?_⟩
  intro x
  cases x with
  | inl x =>
    have hpos := h.2.2.2 x
    change (t.posA x).val=if (s.posA x).val=min s.cursor.val (a-1)
      then min s.cursor.val (a-1)+1
      else if (s.posA x).val=min s.cursor.val (a-1)+1
        then min s.cursor.val (a-1) else (s.posA x).val at hpos
    dsimp only [physicalPosition]
    unfold physicalSwapPosition
    simpa only [hmin] using hpos
  | inr x =>
    dsimp only [physicalPosition]
    unfold physicalSwapPosition
    simp only [hp]
    split_ifs <;> omega

theorem exchangeB_physical (ha : 0<a) (hb : 0<b) {s t : TwoState a b}
    (h : Exchange (projectB hb s) (projectB hb t))
    (hc : t.cursor=s.cursor) (hh : t.winding=s.winding) (hp : t.posA=s.posA) :
    PhysicalX s t := by
  have hx := h.1
  change (if s.cursor.val<a then b-1 else s.cursor.val-a)+1<b at hx
  have hi : a≤s.cursor.val := by
    by_contra he
    have he' : s.cursor.val<a := by omega
    simp only [he',ite_true] at hx
    omega
  have hn : ¬s.cursor.val<a := by omega
  simp only [hn,ite_false] at hx
  refine ⟨hc,hh,by omega,by omega,?_⟩
  intro x
  cases x with
  | inl x =>
    have hxl := (s.posA x).isLt
    dsimp only [physicalPosition]
    unfold physicalSwapPosition
    simp only [hp]
    split_ifs <;> omega
  | inr x =>
    have hpos := h.2.2.2 x
    change (t.posB x).val=if (s.posB x).val=(if s.cursor.val<a then b-1 else s.cursor.val-a)
      then (if s.cursor.val<a then b-1 else s.cursor.val-a)+1
      else if (s.posB x).val=(if s.cursor.val<a then b-1 else s.cursor.val-a)+1
        then (if s.cursor.val<a then b-1 else s.cursor.val-a) else (s.posB x).val at hpos
    simp only [hn,ite_false] at hpos
    dsimp only [physicalPosition]
    unfold physicalSwapPosition
    split_ifs at hpos ⊢ <;> omega

theorem physicalX_step (ha : 0<a) (hb : 0<b) {s t : TwoState a b}
    (h : PhysicalX s t) : Step ha hb s .X t := by
  obtain ⟨hc,hh,hend,hcut,hpos⟩ := h
  by_cases hi : s.cursor.val+1<a
  · have hm : min s.cursor.val (a-1)=s.cursor.val := by omega
    have hB : t.posB=s.posB := by
      apply Equiv.ext
      intro x
      apply Fin.ext
      have he := hpos (.inr x)
      dsimp only [physicalPosition] at he
      unfold physicalSwapPosition at he
      split_ifs at he <;> omega
    apply Step.exchangeA ?_ hc hh hB
    refine ⟨?_,?_,hh,?_⟩
    · change min s.cursor.val (a-1)+1<a
      omega
    · apply Fin.ext
      simp [projectA,hc]
    · intro x
      have he := hpos (.inl x)
      dsimp only [physicalPosition] at he
      unfold physicalSwapPosition at he
      dsimp only [projectA]
      simpa only [hm] using he
  · have hin : a≤s.cursor.val := by omega
    have hn : ¬s.cursor.val<a := by omega
    have hA : t.posA=s.posA := by
      apply Equiv.ext
      intro x
      apply Fin.ext
      have he := hpos (.inl x)
      have hx := (s.posA x).isLt
      dsimp only [physicalPosition] at he
      unfold physicalSwapPosition at he
      split_ifs at he <;> omega
    apply Step.exchangeB ?_ hc hh hA
    refine ⟨?_,?_,?_,?_⟩
    · change (if s.cursor.val<a then b-1 else s.cursor.val-a)+1<b
      simp only [hn,ite_false]
      omega
    · apply Fin.ext
      simp [projectB,hc]
    · simp [projectB,hc,hh]
    · intro x
      have he := hpos (.inr x)
      dsimp only [physicalPosition] at he
      unfold physicalSwapPosition at he
      change (t.posB x).val=if (s.posB x).val=(if s.cursor.val<a then b-1 else s.cursor.val-a)
        then (if s.cursor.val<a then b-1 else s.cursor.val-a)+1
        else if (s.posB x).val=(if s.cursor.val<a then b-1 else s.cursor.val-a)+1
          then (if s.cursor.val<a then b-1 else s.cursor.val-a) else (s.posB x).val
      simp only [hn,ite_false]
      split_ifs at he ⊢ <;> omega

theorem step_X_iff_physical (ha : 0<a) (hb : 0<b) {s t : TwoState a b} :
    Step ha hb s .X t ↔ PhysicalX s t := by
  constructor
  · intro h
    cases h with
    | exchangeA h hc hh hp => exact exchangeA_physical ha hb h hc hh hp
    | exchangeB h hc hh hp => exact exchangeB_physical ha hb h hc hh hp
  · exact physicalX_step ha hb

/-- A second, entirely global definition of physical steps, with no projection
in its constructors. It is equivalent to the proof-oriented Step above. -/
inductive PhysicalStep : TwoState a b → Op → TwoState a b → Prop where
  | left {s t} : Left s t → PhysicalStep s .L t
  | right {s t} : Left t s → PhysicalStep s .R t
  | exchange {s t} : PhysicalX s t → PhysicalStep s .X t

inductive PhysicalTrace : TwoState a b → List Op → TwoState a b → Prop where
  | nil (s) : PhysicalTrace s [] s
  | cons {s m t op w} : PhysicalStep s op m → PhysicalTrace m w t →
      PhysicalTrace s (op::w) t

theorem physical_step_iff (ha : 0<a) (hb : 0<b) {s t : TwoState a b} {op : Op} :
    PhysicalStep s op t ↔ Step ha hb s op t := by
  constructor
  · intro h
    cases h with
    | left h => exact .left h
    | right h => exact .right h
    | exchange h => exact physicalX_step ha hb h
  · intro h
    cases h with
    | left h => exact .left h
    | right h => exact .right h
    | exchangeA h hc hh hp => exact .exchange (exchangeA_physical ha hb h hc hh hp)
    | exchangeB h hc hh hp => exact .exchange (exchangeB_physical ha hb h hc hh hp)

theorem physical_trace_iff (ha : 0<a) (hb : 0<b) {s t : TwoState a b} {w : List Op} :
    PhysicalTrace s w t ↔ Trace ha hb s w t := by
  constructor
  · intro h
    induction h with
    | nil s => exact .nil s
    | cons hs _ ih => exact .cons ((physical_step_iff ha hb).mp hs) ih
  · intro h
    induction h with
    | nil s => exact .nil s
    | cons hs _ ih => exact .cons ((physical_step_iff ha hb).mpr hs) ih

/-- Main physical two-block theorem, stated without any projected trace or
transport inequality among its hypotheses. -/
theorem physical_two_block_rotation_lower (ha : 2≤a) (hb : 2≤b)
    {s t : TwoState a b} {w : List Op} (h : PhysicalTrace s w t)
    (hsA : ∀ x, (s.posA x).val=x.val) (hsB : ∀ x, (s.posB x).val=x.val)
    (htA : ∀ x, (t.posA x).val+x.val+1=a)
    (htB : ∀ x, (t.posB x).val+x.val+1=b)
    (hp : (s.cursor.val+t.cursor.val+2)%(a+b)=a) :
    (a*a+b*b)/2≤rotations w ∧ a*b≤rotations w :=
  two_block_rotation_lower_mod ha hb ((physical_trace_iff (by omega) (by omega)).mp h)
    hsA hsB htA htB hp

def exchanges : List Op → Nat
  | [] => 0
  | .X::w => 1+exchanges w
  | .L::w | .R::w => exchanges w

theorem every_letter_charged (w : List Op) : rotations w+exchanges w=w.length := by
  induction w with
  | nil => rfl
  | cons op w ih => cases op <;> simp [rotations,price,exchanges] at ih ⊢ <;> omega

theorem physical_two_block_price_lower (ha : 2≤a) (hb : 2≤b)
    {s t : TwoState a b} {w : List Op} (h : PhysicalTrace s w t)
    (hsA : ∀ x, (s.posA x).val=x.val) (hsB : ∀ x, (s.posB x).val=x.val)
    (htA : ∀ x, (t.posA x).val+x.val+1=a)
    (htB : ∀ x, (t.posB x).val+x.val+1=b)
    (hp : (s.cursor.val+t.cursor.val+2)%(a+b)=a) :
    (a*a+b*b)/2+exchanges w≤w.length ∧ a*b+exchanges w≤w.length := by
  have hbound := physical_two_block_rotation_lower ha hb h hsA hsB htA htB hp
  have hcount := every_letter_charged w
  omega

#print axioms left_partition
#print axioms step_projection
#print axioms trace_projection
#print axioms trace_projection_with_visits
#print axioms projected_phases
#print axioms mirrorPhase_iff_mod
#print axioms two_block_unrounded
#print axioms trace_cursor_parity
#print axioms odd_blocks_odd_rotations
#print axioms round_two_block_budget
#print axioms two_block_rotation_lower
#print axioms two_block_rotation_lower_mod
#print axioms step_X_iff_physical
#print axioms physical_trace_iff
#print axioms physical_two_block_rotation_lower
#print axioms every_letter_charged
#print axioms physical_two_block_price_lower
end LRX.LowerBoundPaidProjection
