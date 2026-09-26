import UpperBufferNative
import UpperBufferState
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.List.Nodup

/-! Positive native-list lift, with arbitrary integer winding per occurrence.
Preservation below is exact for paid L/R/X, not a service or global budget. -/
namespace LRX.UpperNativeLift
open LRX.BlockExchange
variable {α : Type*}

/-- Every native occurrence has its positive-index integer lift. -/
def Represents (n : Nat) (H : Int) (xs : List α) (z : α → Int) : Prop :=
  ∀ (i : Nat) (hi : i < xs.length), ∃ w : Int,
    z xs[i] = H + (i : Int) + (n : Int) * w

/-- Non-vacuity for every duplicate-free native list and arbitrary windings. -/
theorem canonical [DecidableEq α] (xs : List α) (hn : xs.Nodup)
    (H : Int) (w : α → Int) :
    Represents xs.length H xs
      (fun a => H + (xs.idxOf a : Int) + (xs.length : Int) * w a) := by
  intro i hi
  refine ⟨w xs[i], ?_⟩
  dsimp only
  rw [hn.idxOf_getElem i]

/-- The represented residue is the native index, not its negative. -/
theorem native_residue (xs : List α) (H : Int) (z : α → Int)
    (h : Represents xs.length H xs z) (i : Nat) (hi : i < xs.length) :
    (z xs[i] - H) % (xs.length : Int) = (i : Int) := by
  obtain ⟨w,hw⟩ := h i hi
  rw [hw]
  have he : H + (i:Int) + (xs.length:Int)*w - H = (i:Int)+(xs.length:Int)*w := by ring
  rw [he, Int.add_emod, Int.mul_emod_right, add_zero, Int.emod_emod]
  apply Int.emod_eq_of_lt
  · omega
  · exact_mod_cast hi

/-- Left rotation advances the head and keeps all physical coordinates. -/
theorem step_L (a : α) (ps : List α) (H : Int) (z : α → Int)
    (h : Represents (ps.length+1) H (a::ps) z) :
    Represents (ps.length+1) (H+1) (step .L (a::ps)) z := by
  change Represents (ps.length+1) (H+1) (ps++[a]) z
  intro i hi
  by_cases hp : i < ps.length
  · obtain ⟨w,hw⟩ := h (i+1) (by simp; omega)
    refine ⟨w, ?_⟩
    simpa [List.getElem_append_left hp, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hw
  · have he : i=ps.length := by simp only [List.length_append, List.length_singleton] at hi; omega
    subst i
    obtain ⟨w,hw⟩ := h 0 (by simp)
    refine ⟨w-1, ?_⟩
    simp only [List.getElem_cons_zero] at hw
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]
    push_cast at hw ⊢
    linear_combination hw

/-- Right rotation decreases the head, including the winding across the seam. -/
theorem step_R (ps : List α) (a : α) (H : Int) (z : α → Int)
    (h : Represents (ps.length+1) H (ps++[a]) z) :
    Represents (ps.length+1) (H-1) (step .R (ps++[a])) z := by
  change Represents (ps.length+1) (H-1) (right (ps++[a])) z
  rw [right_append]
  intro i hi
  cases i with
  | zero =>
    obtain ⟨w,hw⟩ := h ps.length (by simp)
    refine ⟨w+1, ?_⟩
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem_cons_zero] at hw
    simp only [List.getElem_cons_zero]
    push_cast at hw ⊢
    linear_combination hw
  | succ i =>
    have hp : i < ps.length := by simp only [List.length_cons] at hi; omega
    obtain ⟨w,hw⟩ := h i (by simp; omega)
    refine ⟨w, ?_⟩
    simp only [List.getElem_append_left hp] at hw
    simp only [List.getElem_cons_succ, Nat.cast_succ]
    push_cast at hw ⊢
    linear_combination hw

/-- X changes the physical coordinates of just the first two labels. -/
def exchange [DecidableEq α] (a b : α) (z : α → Int) (c : α) : Int :=
  if c=a then z c+1 else if c=b then z c-1 else z c

theorem step_X [DecidableEq α] (a b : α) (ps : List α) (H : Int) (z : α → Int)
    (hn : (a::b::ps).Nodup)
    (h : Represents (ps.length+2) H (a::b::ps) z) :
    Represents (ps.length+2) H (step .X (a::b::ps)) (exchange a b z) := by
  have hab : a ≠ b := by
    intro he
    exact (List.nodup_cons.mp hn).1 (by simp [he])
  have ha : a ∉ ps := by
    intro hm
    exact (List.nodup_cons.mp hn).1 (by simp [hm])
  have hb : b ∉ ps := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
  change Represents (ps.length+2) H (b::a::ps) (exchange a b z)
  intro i hi
  cases i with
  | zero =>
    obtain ⟨w,hw⟩ := h 1 (by simp)
    refine ⟨w, ?_⟩
    simp [exchange, Ne.symm hab] at *
    omega
  | succ i =>
    cases i with
    | zero =>
      obtain ⟨w,hw⟩ := h 0 (by simp)
      refine ⟨w, ?_⟩
      simp [exchange] at *
      omega
    | succ j =>
      have hj : j < ps.length := by simp only [List.length_cons] at hi; omega
      obtain ⟨w,hw⟩ := h (j+2) (by simp; omega)
      have hmem : ps[j] ∈ ps := List.getElem_mem hj
      have hna : ps[j] ≠ a := by intro he; exact ha (he ▸ hmem)
      have hnb : ps[j] ≠ b := by intro he; exact hb (he ▸ hmem)
      refine ⟨w, ?_⟩
      simpa [exchange, hna, hnb, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hw

#print axioms canonical
#print axioms native_residue
#print axioms step_L
#print axioms step_R
#print axioms step_X
end LRX.UpperNativeLift
