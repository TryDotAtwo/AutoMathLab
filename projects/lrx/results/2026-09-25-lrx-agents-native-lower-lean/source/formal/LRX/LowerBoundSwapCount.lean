import LRX.LowerBoundNoRepeat
import LRX.LowerBoundPairParity

/-! Exact pair occurrence counts in shortest concrete LRX words. -/
namespace LRX.LowerBoundSwapCount
open LRX.BlockExchange LRX.Cycle11StructuralBridge
open LRX.LowerBoundNoRepeat LRX.LowerBoundPairParity
variable {α : Type*} [DecidableEq α]

def swapCount (a b : α) : List Op → List α → Nat
  | [], _ => 0
  | op::w, s => (if swapEvent a b op s then 1 else 0) + swapCount a b w (step op s)

theorem pairAtHead_true (a b : α) (s : List α) :
    pairAtHead a b s=true ↔ HeadPair a b s := by
  cases s with
  | nil => simp [pairAtHead,HeadPair]
  | cons x xs => cases xs with
    | nil => simp [pairAtHead,HeadPair]
    | cons y t => simp [pairAtHead,HeadPair]

theorem event_true (a b : α) (op : Op) (s : List α)
    (h : swapEvent a b op s=true) : op=Op.X ∧ HeadPair a b s := by
  cases op with
  | L => simp [swapEvent] at h
  | R => simp [swapEvent] at h
  | X => exact ⟨rfl,(pairAtHead_true a b s).mp h⟩

theorem positive_has_event (a b : α) (w : List Op) (s : List α)
    (h : 0<swapCount a b w s) :
    ∃ u v : List Op, w=u++[.X]++v ∧ HeadPair a b (run u s) := by
  induction w generalizing s with
  | nil => simp [swapCount] at h
  | cons op w ih =>
    cases he : swapEvent a b op s with
    | false =>
      have ht : 0<swapCount a b w (step op s) := by simpa [swapCount,he] using h
      obtain ⟨u,v,hw,hp⟩ := ih (step op s) ht
      refine ⟨op::u,v,?_,?_⟩
      · simp [hw]
      · simpa [run] using hp
    | true =>
      obtain ⟨rfl,hp⟩ := event_true a b op s he
      exact ⟨[],w,rfl,hp⟩

theorem shortest_tail (op : Op) (w : List Op) (s : List α)
    (h : Shortest (op::w) s) : Shortest w (step op s) := by
  intro v hv
  have hh := h (op::v) (by simpa [run] using hv)
  simpa using hh

theorem shortest_count_le_one (a b : α) (w : List Op) (s : List α)
    (hs : s.Nodup) (hmin : Shortest w s) : swapCount a b w s≤1 := by
  induction w generalizing s with
  | nil => simp [swapCount]
  | cons op w ih =>
    have ht := shortest_tail op w s hmin
    have hc := ih (step op s) ((step_perm op s).nodup_iff.mpr hs) ht
    cases he : swapEvent a b op s with
    | false => simpa [swapCount,he] using hc
    | true =>
      obtain ⟨rfl,hp⟩ := event_true a b op s he
      have hz : swapCount a b w (step .X s)=0 := by
        by_contra hn
        have hpos : 0<swapCount a b w (step .X s) := by omega
        obtain ⟨u,v,hw,hsecond⟩ := positive_has_event a b w (step .X s) hpos
        have hsecond' : HeadPair a b (run ([]++[.X]++u) s) := by
          simpa [run] using hsecond
        have hbad := shortest_no_repeated_pair a b s [] u v hs hp hsecond'
        apply hbad
        simpa [hw] using hmin
      simp [swapCount,he,hz]

theorem count_zero_parity (a b : α) (w : List Op) (s : List α)
    (h : swapCount a b w s=0) : swapParity a b w s=false := by
  induction w generalizing s with
  | nil => rfl
  | cons op w ih =>
    cases he : swapEvent a b op s with
    | false =>
      have ht : swapCount a b w (step op s)=0 := by simpa [swapCount,he] using h
      simp [swapParity,he,ih (step op s) ht]
    | true => simp [swapCount,he] at h

theorem parity_of_small_count (a b : α) (w : List Op) (s : List α)
    (h : swapCount a b w s≤1) :
    swapParity a b w s=decide (swapCount a b w s=1) := by
  induction w generalizing s with
  | nil => simp [swapParity,swapCount]
  | cons op w ih =>
    cases he : swapEvent a b op s with
    | false =>
      have ht : swapCount a b w (step op s)≤1 := by simpa [swapCount,he] using h
      simpa [swapParity,swapCount,he] using ih (step op s) ht
    | true =>
      have ht : swapCount a b w (step op s)=0 := by
        simp only [swapCount,he,Bool.true_eq,ite_true] at h
        omega
      simp [swapParity,swapCount,he,ht,count_zero_parity a b w (step op s) ht]

/-- Exact actual counts, not only parity, for every shortest reflected word. -/
theorem shortest_reflection_counts (w v : List Op) (s : List α) (z : α)
    (hs : s.Nodup) (hall : ∀ a : α, a∈s) (hmin : Shortest w s)
    (hv : Rotations v) (hend : run w s=run v s.reverse) :
    ∃ color : α → Bool, ∀ a b : α, a≠b →
      swapCount a b w s=if color a=color b then 1 else 0 := by
  obtain ⟨color,hcolor⟩ := reflection_two_cliques w v s z hs hall hv hend
  refine ⟨color,?_⟩
  intro a b hab
  have hc := shortest_count_le_one a b w s hs hmin
  have hp := parity_of_small_count a b w s hc
  have hh := hcolor a b hab
  rw [hp] at hh
  by_cases he : color a=color b
  · simp [he] at hh ⊢
    exact hh
  · have hbool : (color a == color b)=false := by
      cases ha : color a <;> cases hb : color b <;> simp_all
    rw [hbool] at hh
    have hn : swapCount a b w s≠1 := of_decide_eq_false hh
    simp only [he,ite_false]
    omega

#print axioms positive_has_event
#print axioms shortest_count_le_one
#print axioms parity_of_small_count
#print axioms shortest_reflection_counts
end LRX.LowerBoundSwapCount
