import LRX.LowerBoundNoRepeat
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Rotate
import Mathlib.Tactic.NormNum

/-! Parity of every paid generator at n=4. This is a symbolic invariant
of arbitrary words; no word enumeration or native evaluation is used. -/
namespace LRX.LowerBoundFourParity
open LRX.BlockExchange LRX.Cycle11StructuralBridge LRX.Cycle11TwoLabelRepair

def inversionBit (a b : Nat) : Nat := if b<a then 1 else 0

def inversions4 : List Nat → Nat
  | [a,b,c,d] => inversionBit a b + inversionBit a c + inversionBit a d +
      inversionBit b c + inversionBit b d + inversionBit c d
  | _ => 0

theorem inversionBit_complement (a b : Nat) (h : a≠b) :
    inversionBit a b + inversionBit b a = 1 := by
  unfold inversionBit
  split_ifs <;> omega

theorem step_four_odd (op : Op) (s : List Nat)
    (hs : s.Nodup) (hlen : s.length=4) :
    (inversions4 (step op s)+1)%2 = inversions4 s%2 := by
  cases s with
  | nil => simp at hlen
  | cons a s => cases s with
    | nil => simp at hlen
    | cons b s => cases s with
      | nil => simp at hlen
      | cons c s => cases s with
        | nil => simp at hlen
        | cons d s =>
          have he : s=[] := by apply List.eq_nil_of_length_eq_zero; simpa using hlen
          subst s
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
            not_or, and_true] at hs
          have hab := inversionBit_complement a b hs.1.1
          have hac := inversionBit_complement a c hs.1.2.1
          have had := inversionBit_complement a d hs.1.2.2
          have hbc := inversionBit_complement b c hs.2.1.1
          have hbd := inversionBit_complement b d hs.2.1.2
          have hcd := inversionBit_complement c d hs.2.2.1
          cases op <;> simp only [step, left, right, swap, List.reverse_cons,
            List.reverse_nil, List.nil_append, List.cons_append, List.append_nil,
            inversions4] <;> omega

theorem run_four_parity (w : List Op) (s : List Nat)
    (hs : s.Nodup) (hlen : s.length=4) :
    (inversions4 (run w s)+w.length)%2 = inversions4 s%2 := by
  induction w generalizing s with
  | nil => simp [run]
  | cons op w ih =>
    have hp := step_perm op s
    have ht := ih (step op s) (hp.nodup_iff.mpr hs) (hp.length_eq.trans hlen)
    have ho := step_four_odd op s hs hlen
    simp only [run, List.length_cons]
    omega

theorem four_native_even (w : List Op)
    (hend : run w ([0,1,2,3] : List Nat) = [1,0,3,2]) :
    w.length%2=0 := by
  have h := run_four_parity w [0,1,2,3] (by decide) rfl
  rw [hend] at h
  norm_num [inversions4, inversionBit] at h
  omega

/-- The original reflected target, with 0-based Fin labels. -/
theorem four_fin_native_even (w : List Op)
    (hend : run w (List.finRange 4) = (List.finRange 4).reverse.rotate 2) :
    w.length%2=0 := by
  apply four_native_even w
  have h := congrArg (List.map Fin.val) hend
  rw [← run_map] at h
  simpa [List.finRange_succ, List.rotate] using h

#print axioms step_four_odd
#print axioms run_four_parity
#print axioms four_fin_native_even
end LRX.LowerBoundFourParity
