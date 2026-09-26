import LRX.Cycle11BlockReversal

/-! Two separately valid projection words have total rotation price k²-4.
This asserts separate endpoints, never a common lift or an original short word.
Monotonicity of the shell construction is documented mathematically outside
this module; the kernel theorem below checks actual words and every rotation. -/
namespace LRX.LowerBoundProjectionBarrier
open LRX.BlockExchange LRX.ReducedPrice LRX.Cycle11BlockReversal
variable {α : Type*}

def rotCount : List Op → Nat
  | [] => 0
  | .L::w => 1+rotCount w
  | .R::w => 1+rotCount w
  | .X::w => rotCount w

theorem rot_append (u v : List Op) : rotCount (u++v)=rotCount u+rotCount v := by
  induction u with
  | nil => simp [rotCount]
  | cons op u ih => cases op <;> simp [rotCount,ih,Nat.add_assoc]

theorem rot_replicate_L (n : Nat) : rotCount (List.replicate n .L)=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,rotCount,ih,Nat.add_comm]

theorem rot_replicate_R (n : Nat) : rotCount (List.replicate n .R)=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,rotCount,ih,Nat.add_comm]

theorem rot_spin (x : Int) : rotCount (spin x)=x.natAbs := by
  cases x <;> simp [spin,rot_replicate_L,rot_replicate_R]

theorem rot_ends (k : Nat) : rotCount (ends k)=2*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [ends,rot_append,rotCount,ih];omega

theorem zig_alternation_count (k : Nat) (hk : 2≤k) :
    (zig k).length=2*rotCount (zig k)+1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 => omega
    | 1 => omega
    | 2 => rfl
    | 3 => rfl
    | k+4 =>
      have h := ih (k+2) (by omega) (by omega)
      simp only [zig,List.length_append,List.length_cons,List.length_nil,
        ends_length,rot_append,rotCount,rot_ends]
      omega

def projectedA (k : Nat) : List Op :=
  zig k ++ spin ((k-2-offset k : Nat) : Int)
def projectedB (k : Nat) : List Op :=
  zig k ++ spin (-(offset k : Int))

theorem separate_endpoints (k : Nat) (p : List α) (hk : 2≤k) (hp : p.length=k) :
    run (projectedA k) p=run (spin ((k-2 : Nat) : Int)) p.reverse ∧
    run (projectedB k) p=p.reverse := by
  have hz : run (zig k) p=run (spin (offset k : Int)) p.reverse := by
    simpa using zig_run k p [] hp
  have ho := offset_formula k hk
  have hle : offset k≤k-2 := by omega
  constructor
  · rw [projectedA,run_append,hz,←spin_add]
    have he : (offset k : Int)+((k-2-offset k : Nat) : Int)=((k-2 : Nat) : Int) := by omega
    rw [he]
  · rw [projectedB,run_append,hz,←spin_add]
    simp [spin,run]

theorem separate_rotation_budget (k : Nat) (hk : 2≤k) :
    rotCount (projectedA k)+rotCount (projectedB k)+4=k*k := by
  have hz := zig_length k hk
  have ha := zig_alternation_count k hk
  have ho := offset_formula k hk
  have hle : offset k≤k-2 := by omega
  simp only [projectedA,projectedB,rot_append,rot_spin,Int.natAbs_neg,Int.natAbs_natCast]
  have hs : k-1+1=k := by omega
  have hs2 : k-2+2=k := by omega
  have htail : k-2-offset k+offset k=k-2 := by omega
  nlinarith

/-- A simultaneous existential assertion of TWO independent words, with no
claim that they are projections of one common physical cursor trace. -/
theorem separate_words (k : Nat) (p : List α) (hk : 2≤k) (hp : p.length=k) :
    ∃ a b : List Op,
      run a p=run (spin ((k-2 : Nat) : Int)) p.reverse ∧
      run b p=p.reverse ∧ rotCount a+rotCount b+4=k*k := by
  have h := separate_endpoints k p hk hp
  exact ⟨projectedA k,projectedB k,h.1,h.2,separate_rotation_budget k hk⟩

#print axioms zig_alternation_count
#print axioms separate_endpoints
#print axioms separate_rotation_budget
#print axioms separate_words
end LRX.LowerBoundProjectionBarrier
