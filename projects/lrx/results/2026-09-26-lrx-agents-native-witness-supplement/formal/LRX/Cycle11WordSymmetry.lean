import LRX.Cycle11StructuralBridge

namespace LRX.Cycle11WordSymmetry
open LRX.BlockExchange LRX.ReducedPrice
variable {α : Type*}

def mirrorOp : Op → Op
  | .L => .R
  | .R => .L
  | .X => .X
def mirror (w : List Op) := w.map mirrorOp
def inverse (w : List Op) := mirror w.reverse

def reflect : List α → List α
  | a::b::t => b::a::t.reverse
  | t => t

theorem reflect_involutive (s : List α) : reflect (reflect s)=s := by
  cases s with
  | nil => rfl
  | cons a t => cases t <;> simp [reflect]

theorem reflect_left (s : List α) : reflect (left s)=right (reflect s) := by
  cases s with
  | nil => rfl
  | cons a t => cases t with
    | nil => rfl
    | cons b t => cases t <;> simp [reflect,left,right,List.append_assoc]

theorem reflect_right (s : List α) : reflect (right s)=left (reflect s) := by
  have h := reflect_left (right s)
  rw [left_right] at h
  have hh := congrArg left h
  simpa [left_right] using hh.symm

theorem reflect_step (op : Op) (s : List α) :
    reflect (step op s)=step (mirrorOp op) (reflect s) := by
  cases op with
  | L => exact reflect_left s
  | R => exact reflect_right s
  | X => cases s with
    | nil => rfl
    | cons a t => cases t <;> rfl

theorem reflect_run (w : List Op) (s : List α) :
    reflect (run w s)=run (mirror w) (reflect s) := by
  induction w generalizing s with
  | nil => rfl
  | cons op w ih => simpa [run,mirror,reflect_step] using ih (step op s)

theorem step_inverse (op : Op) (s : List α) : step (mirrorOp op) (step op s)=s := by
  cases op with
  | L => exact right_left s
  | R => exact left_right s
  | X => cases s with
    | nil => rfl
    | cons a t => cases t <;> rfl

theorem run_inverse (w : List Op) (s : List α) : run (inverse w) (run w s)=s := by
  induction w generalizing s with
  | nil => rfl
  | cons op w ih =>
    simp only [inverse,mirror,List.reverse_cons,List.map_append,List.map_cons,List.map_nil,run_append,run]
    change run [mirrorOp op] (run (inverse w) (run w (step op s))) = _
    rw [ih]
    exact step_inverse op s

theorem inverse_mirror (w : List Op) : inverse (mirror w)=w.reverse := by
  simp only [inverse,mirror,List.map_reverse,List.map_map]
  have h : mirrorOp ∘ mirrorOp = id := by funext op; cases op <;> rfl
  rw [h,List.map_id]

theorem reflect_as_reverse (s : List α) : reflect s=run (spin (-2)) s.reverse := by
  change reflect s=run [.R,.R] s.reverse
  cases s with
  | nil => rfl
  | cons a t => cases t <;> simp [reflect,spin,run,step,right,left,List.append_assoc]

theorem mirror_spin (k : Int) : mirror (spin k)=spin (-k) := by
  cases k with
  | ofNat n =>
    change mirror (List.replicate n .L)=spin (-(n : Int))
    rw [spin_neg_nat]
    simp [mirror,mirrorOp]
  | negSucc n =>
    change mirror (List.replicate (n+1) .R)=spin ((n+1 : Nat) : Int)
    rw [spin_nat]
    simp [mirror,mirrorOp]

theorem reflect_spin (k : Int) (s : List α) :
    reflect (run (spin k) s)=run (spin (-k)) (reflect s) := by
  rw [reflect_run,mirror_spin]

theorem reverse_spin (k : Int) (s : List α) :
    (run (spin k) s).reverse=run (spin (-k)) s.reverse := by
  have h := reflect_spin k s
  simp only [reflect_as_reverse] at h
  have hi := congrArg (run (spin (2 : Int))) h
  simp only [←spin_add] at hi
  simpa [spin,run] using hi

theorem spin_length_state (k : Int) (s : List α) : (run (spin k) s).length=s.length :=
  (LRX.Cycle11StructuralBridge.run_perm (spin k) s).length_eq

theorem spin_prefix (p rest : List α) :
    run (spin (p.length : Int)) (p++rest)=rest++p := by
  induction p generalizing rest with
  | nil => simp [spin,run]
  | cons a p ih =>
    have h : ((a::p).length : Int)=1+(p.length : Int) := by simp; omega
    rw [h,spin_add]
    simpa [spin,run,step,left,List.append_assoc] using ih (rest++[a])

#print axioms reflect_run
#print axioms run_inverse
#print axioms reverse_spin
#print axioms spin_prefix
end LRX.Cycle11WordSymmetry
