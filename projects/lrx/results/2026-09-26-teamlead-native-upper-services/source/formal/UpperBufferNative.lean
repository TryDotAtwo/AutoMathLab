import LRX.BlockExchange
import Mathlib.Data.List.Induction

/-! Exact native semantics of the logical-buffer macros. No service existence claimed. -/
namespace LRX.UpperBufferNative
open LRX.BlockExchange
variable {α : Type*}

def U : List Op := [.X,.L]
def V : List Op := [.R,.X]

theorem run_U (a : α) (ps : List α) : run U (a::ps)=a::left ps := by
  cases ps <;> simp [U,run,step,swap,left]

theorem run_V (a : α) (ps : List α) : run V (a::ps)=a::right ps := by
  induction ps using List.reverseRecOn with
  | nil => rfl
  | append_singleton ps b ih =>
    have h : a::(ps++[b])=(a::ps)++[b] := rfl
    change swap (right (a::(ps++[b]))) = a::right (ps++[b])
    rw [h, right_append, right_append]
    rfl

def forward : Nat → List Op
  | 0 => []
  | k+1 => U ++ forward k

def backward : Nat → List Op
  | 0 => []
  | k+1 => V ++ backward k

theorem run_forward (k : Nat) (a : α) (ps : List α) :
    run (forward k) (a::ps)=a::(left^[k]) ps := by
  induction k generalizing ps with
  | zero => rfl
  | succ k ih =>
    rw [forward,run_append,run_U,ih]
    simp [Function.iterate_succ_apply]

theorem run_backward (k : Nat) (a : α) (ps : List α) :
    run (backward k) (a::ps)=a::(right^[k]) ps := by
  induction k generalizing ps with
  | zero => rfl
  | succ k ih =>
    rw [backward,run_append,run_V,ih]
    simp [Function.iterate_succ_apply]

theorem forward_length (k : Nat) : (forward k).length=2*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [forward,U,ih]; omega

theorem backward_length (k : Nat) : (backward k).length=2*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [backward,V,ih]; omega

#print axioms run_U
#print axioms run_V
#print axioms run_forward
#print axioms run_backward
#print axioms forward_length
#print axioms backward_length
end LRX.UpperBufferNative
