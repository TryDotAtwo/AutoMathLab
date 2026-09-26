import LRX.Cycle11StructuralBridge
import LRX.LowerBoundSwapGraph

/-! Parity bookkeeping from the actual LRX trace, not an abstract graph premise. -/
namespace LRX.LowerBoundPairParity
open LRX.BlockExchange LRX.Cycle11StructuralBridge
variable {α : Type*} [DecidableEq α]

/-- Relative order bit: false if a is met first, true if b is met first.
The lemmas that interpret it assume both labels are present and distinct. -/
def beforeBit (a b : α) : List α → Bool
  | [] => false
  | x::xs => if x=a then false else if x=b then true else beforeBit a b xs

def headIs (a : α) : List α → Bool
  | [] => false
  | x::_ => decide (x=a)

def pairAtHead (a b : α) : List α → Bool
  | x::y::_ => (decide (x=a) && decide (y=b)) || (decide (x=b) && decide (y=a))
  | _ => false

def turnEvent (a : α) (op : Op) (s : List α) : Bool :=
  match op with
  | .L => headIs a s
  | .R => headIs a (right s)
  | .X => false

def swapEvent (a b : α) (op : Op) (s : List α) : Bool :=
  match op with
  | .X => pairAtHead a b s
  | _ => false

theorem bit_append (a b : α) (s t : List α) (h : a∈s ∨ b∈s) :
    beforeBit a b (s++t)=beforeBit a b s := by
  induction s with
  | nil => simp at h
  | cons x xs ih =>
    by_cases ha : x=a
    · simp [beforeBit,ha]
    · by_cases hb : x=b
      · simp [beforeBit,hb]
      · have ht : a∈xs ∨ b∈xs := by
          simpa only [List.mem_cons,Ne.symm ha,Ne.symm hb,false_or] using h
        simpa [beforeBit,ha,hb] using ih ht

theorem bit_false_of_b_absent (a b : α) (s : List α) (hb : b∉s) :
    beforeBit a b s=false := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
    have hx : x≠b := by intro he;subst x;exact hb (by simp)
    have ht : b∉xs := fun h => hb (List.mem_cons_of_mem x h)
    simp [beforeBit,hx,ih ht]

theorem bit_true_of_a_absent (a b : α) (s : List α) (ha : a∉s) (hb : b∈s) :
    beforeBit a b s=true := by
  induction s with
  | nil => simp at hb
  | cons x xs ih =>
    have hx : x≠a := by intro he;subst x;exact ha (by simp)
    by_cases hy : x=b
    · subst x
      simp [beforeBit,hx]
    · have ht : b∈xs := by simpa only [List.mem_cons,Ne.symm hy,false_or] using hb
      have hn : a∉xs := fun h => ha (List.mem_cons_of_mem x h)
      simpa [beforeBit,hx,hy] using ih hn ht

theorem bit_left (a b : α) (s : List α) (hab : a≠b)
    (hs : s.Nodup) (ha : a∈s) (hb : b∈s) :
    beforeBit a b (left s)=(beforeBit a b s ^^ (headIs a s ^^ headIs b s)) := by
  cases s with
  | nil => simp at ha
  | cons x xs =>
    have hn : x∉xs := (List.nodup_cons.mp hs).1
    by_cases hxa : x=a
    · subst x
      have hbt : b∈xs := by simpa only [List.mem_cons,Ne.symm hab,false_or] using hb
      rw [left,bit_append a b xs [a] (Or.inr hbt)]
      rw [bit_true_of_a_absent a b xs hn hbt]
      simp [beforeBit,headIs,hab]
    · by_cases hxb : x=b
      · subst x
        have hat : a∈xs := by simpa only [List.mem_cons,hab,false_or] using ha
        rw [left,bit_append a b xs [b] (Or.inl hat)]
        rw [bit_false_of_b_absent a b xs hn]
        simp [beforeBit,headIs,hxa]
      · have hat : a∈xs := by simpa only [List.mem_cons,Ne.symm hxa,false_or] using ha
        rw [left,bit_append a b xs [x] (Or.inl hat)]
        simp [beforeBit,headIs,hxa,hxb]

theorem bit_swap (a b : α) (s : List α) (hab : a≠b) :
    beforeBit a b (swap s)=(beforeBit a b s ^^ pairAtHead a b s) := by
  cases s with
  | nil => rfl
  | cons x xs => cases xs with
    | nil => simp [swap,pairAtHead]
    | cons y t =>
      by_cases hxa : x=a <;> by_cases hxb : x=b <;>
        by_cases hya : y=a <;> by_cases hyb : y=b <;>
        simp_all [swap,beforeBit,pairAtHead]

theorem bit_right (a b : α) (s : List α) (hab : a≠b)
    (hs : s.Nodup) (ha : a∈s) (hb : b∈s) :
    beforeBit a b (right s)=(beforeBit a b s ^^
      (headIs a (right s) ^^ headIs b (right s))) := by
  have hp : (right s).Perm s := step_perm .R s
  have h := bit_left a b (right s) hab (hp.nodup_iff.mpr hs)
    (hp.mem_iff.mpr ha) (hp.mem_iff.mpr hb)
  rw [LRX.ReducedPrice.left_right] at h
  cases h0 : beforeBit a b s <;> cases h1 : beforeBit a b (right s) <;>
    cases h2 : headIs a (right s) <;> cases h3 : headIs b (right s) <;> simp_all

theorem bit_step (a b : α) (op : Op) (s : List α) (hab : a≠b)
    (hs : s.Nodup) (ha : a∈s) (hb : b∈s) :
    beforeBit a b (step op s)=(beforeBit a b s ^^
      (turnEvent a op s ^^ turnEvent b op s ^^ swapEvent a b op s)) := by
  cases op with
  | L => simpa [step,turnEvent,swapEvent] using bit_left a b s hab hs ha hb
  | R => simpa [step,turnEvent,swapEvent] using bit_right a b s hab hs ha hb
  | X => simpa [step,turnEvent,swapEvent] using bit_swap a b s hab

def turnParity (a : α) : List Op → List α → Bool
  | [], _ => false
  | op::w, s => turnEvent a op s ^^ turnParity a w (step op s)

def swapParity (a b : α) : List Op → List α → Bool
  | [], _ => false
  | op::w, s => swapEvent a b op s ^^ swapParity a b w (step op s)

/-- Exact parity identity for every actual LRX word, with arbitrary cancellations. -/
theorem bit_run (a b : α) (w : List Op) (s : List α) (hab : a≠b)
    (hs : s.Nodup) (ha : a∈s) (hb : b∈s) :
    beforeBit a b (run w s)=(beforeBit a b s ^^
      (turnParity a w s ^^ turnParity b w s ^^ swapParity a b w s)) := by
  induction w generalizing s with
  | nil => simp [run,turnParity,swapParity]
  | cons op w ih =>
    have hp := step_perm op s
    have ht := ih (step op s) (hp.nodup_iff.mpr hs)
      (hp.mem_iff.mpr ha) (hp.mem_iff.mpr hb)
    rw [run,ht,bit_step a b op s hab hs ha hb]
    simp only [turnParity,swapParity,Bool.xor_assoc,Bool.xor_left_comm,Bool.xor_comm]

theorem bit_reverse (a b : α) (s : List α) (hab : a≠b)
    (hs : s.Nodup) (ha : a∈s) (hb : b∈s) :
    beforeBit a b s.reverse= !(beforeBit a b s) := by
  induction s with
  | nil => simp at ha
  | cons x xs ih =>
    have hn := (List.nodup_cons.mp hs).1
    have hnt := (List.nodup_cons.mp hs).2
    by_cases hxa : x=a
    · subst x
      have hbt : b∈xs := by simpa only [List.mem_cons,Ne.symm hab,false_or] using hb
      have hbr : b∈xs.reverse := by simpa using hbt
      have har : a∉xs.reverse := by simpa using hn
      rw [List.reverse_cons,bit_append a b xs.reverse [a] (Or.inr hbr)]
      rw [bit_true_of_a_absent a b xs.reverse har hbr]
      simp [beforeBit]
    · by_cases hxb : x=b
      · subst x
        have hat : a∈xs := by simpa only [List.mem_cons,hab,false_or] using ha
        have har : a∈xs.reverse := by simpa using hat
        have hbr : b∉xs.reverse := by simpa using hn
        rw [List.reverse_cons,bit_append a b xs.reverse [b] (Or.inl har)]
        rw [bit_false_of_b_absent a b xs.reverse hbr]
        simp [beforeBit,hxa]
      · have hat : a∈xs := by simpa only [List.mem_cons,Ne.symm hxa,false_or] using ha
        have hbt : b∈xs := by simpa only [List.mem_cons,Ne.symm hxb,false_or] using hb
        have har : a∈xs.reverse := by simpa using hat
        rw [List.reverse_cons,bit_append a b xs.reverse [x] (Or.inl har)]
        simpa [beforeBit,hxa,hxb] using ih hnt hat hbt

def Rotations (w : List Op) : Prop := ∀ op∈w, op≠Op.X

theorem swapParity_rotations (a b : α) (w : List Op) (s : List α)
    (hr : Rotations w) : swapParity a b w s=false := by
  induction w generalizing s with
  | nil => rfl
  | cons op w ih =>
    have ho : op≠Op.X := hr op (by simp)
    have ht : Rotations w := fun x hx => hr x (List.mem_cons_of_mem op hx)
    cases op <;> simp_all [swapParity,swapEvent]

theorem pairAtHead_symm (a b : α) (s : List α) :
    pairAtHead a b s=pairAtHead b a s := by
  cases s with
  | nil => rfl
  | cons x xs => cases xs with
    | nil => rfl
    | cons y t => simp only [pairAtHead,Bool.or_comm]

theorem swapParity_symm (a b : α) (w : List Op) (s : List α) :
    swapParity a b w s=swapParity b a w s := by
  induction w generalizing s with
  | nil => rfl
  | cons op w ih =>
    have he : swapEvent a b op s=swapEvent b a op s := by
      cases op <;> simp [swapEvent,pairAtHead_symm]
    simp only [swapParity,he,ih]

def tripleBit (a b c : α) (s : List α) : Bool :=
  beforeBit a b s ^^ beforeBit a c s ^^ beforeBit b c s

theorem triple_run (a b c : α) (w : List Op) (s : List α)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (hs : s.Nodup) (ha : a∈s) (hb : b∈s) (hc : c∈s) :
    tripleBit a b c (run w s)=(tripleBit a b c s ^^
      (swapParity a b w s ^^ swapParity a c w s ^^ swapParity b c w s)) := by
  simp only [tripleBit,bit_run a b w s hab hs ha hb,
    bit_run a c w s hac hs ha hc,bit_run b c w s hbc hs hb hc]
  simp only [Bool.xor_assoc,Bool.xor_left_comm,Bool.xor_comm]
  cases turnParity a w s <;> cases turnParity b w s <;> cases turnParity c w s <;> simp

theorem triple_reverse (a b c : α) (s : List α)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (hs : s.Nodup) (ha : a∈s) (hb : b∈s) (hc : c∈s) :
    tripleBit a b c s.reverse= !(tripleBit a b c s) := by
  simp only [tripleBit,bit_reverse a b s hab hs ha hb,
    bit_reverse a c s hac hs ha hc,bit_reverse b c s hbc hs hb hc]
  cases beforeBit a b s <;> cases beforeBit a c s <;> cases beforeBit b c s <;> rfl

/-- Reflected cyclic endpoints force odd swap parity on every triple.
The endpoint and every parity are computed from the same actual LRX word. -/
theorem reflection_swap_triangle (a b c : α) (w v : List Op) (s : List α)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (hs : s.Nodup) (ha : a∈s) (hb : b∈s) (hc : c∈s)
    (hv : Rotations v) (hend : run w s=run v s.reverse) :
    ((swapParity a b w s ^^ swapParity a c w s) ^^ swapParity b c w s)=true := by
  have hsr : s.reverse.Nodup := hs.reverse.imp (fun h => Ne.symm h)
  have har : a∈s.reverse := by simpa using ha
  have hbr : b∈s.reverse := by simpa using hb
  have hcr : c∈s.reverse := by simpa using hc
  have hrot := triple_run a b c v s.reverse hab hac hbc hsr har hbr hcr
  simp only [swapParity_rotations a b v s.reverse hv,
    swapParity_rotations a c v s.reverse hv,swapParity_rotations b c v s.reverse hv,
    Bool.xor_false,Bool.false_xor] at hrot
  have hf : tripleBit a b c (run w s)= !(tripleBit a b c s) := by
    rw [hend,hrot]
    exact triple_reverse a b c s hab hac hbc hs ha hb hc
  rw [triple_run a b c w s hab hac hbc hs ha hb hc] at hf
  cases ht : tripleBit a b c s <;>
    cases he : ((swapParity a b w s ^^ swapParity a c w s) ^^ swapParity b c w s) <;>
    simp_all

/-- No parity-graph axiom is assumed: the two-clique partition is derived
from the concrete distinct-label reflected endpoint and paid LRX trace. -/
theorem reflection_two_cliques (w v : List Op) (s : List α) (z : α)
    (hs : s.Nodup) (hall : ∀ a : α, a∈s)
    (hv : Rotations v) (hend : run w s=run v s.reverse) :
    ∃ color : α → Bool, ∀ a b : α, a≠b →
      swapParity a b w s=(color a == color b) := by
  refine ⟨LRX.LowerBoundSwapGraph.color (fun a b => swapParity a b w s) z,?_⟩
  intro a b hab
  exact LRX.LowerBoundSwapGraph.two_cliques (fun a b => swapParity a b w s) z
    (fun a b => swapParity_symm a b w s)
    (fun a b c hab hac hbc => reflection_swap_triangle a b c w v s hab hac hbc
      hs (hall a) (hall b) (hall c) hv hend) a b hab

#print axioms bit_step
#print axioms bit_run
#print axioms bit_reverse
#print axioms swapParity_rotations
#print axioms swapParity_symm
#print axioms triple_run
#print axioms triple_reverse
#print axioms reflection_swap_triangle
#print axioms reflection_two_cliques
end LRX.LowerBoundPairParity
