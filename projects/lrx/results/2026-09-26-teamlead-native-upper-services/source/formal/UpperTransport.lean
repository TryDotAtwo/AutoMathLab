import UpperLogicalStep

/-! Constructive paid forward transport; no subtree service or global U. -/
namespace LRX.UpperNativeLift
open LRX.BlockExchange LRX.UpperBufferNative
open LRX.UpperAffineBuffer (contract)
variable {α : Type*} [DecidableEq α]

/-- Iterating XL is possible for every full native permutation of size at least
 two. The same buffer stays at the head; only its logical coordinate advances.
 No endpoint or coordinate law is assumed. All k macros cost exactly 2*k. -/
theorem forward_transport (k : Nat) (a : α) (ps : List α) (H : Int) (z : α → Int)
    (hne : 1 ≤ ps.length) (hall : ∀ c, c∈a::ps) (hn : (a::ps).Nodup)
    (h : Represents (ps.length+1) H (a::ps) z) :
    ∃ z' : α → Int,
      Represents (ps.length+1) (H+(k:Int)) (run (forward k) (a::ps)) z' ∧
      ∀ c, contract (ps.length:Int) (H+(k:Int)) (z' c) =
        contract (ps.length:Int) H (z c)+(if c=a then (k:Int) else 0) := by
  induction k generalizing ps H z with
  | zero => exact ⟨z, by simpa [forward,run] using h, by intro c; simp⟩
  | succ k ih =>
    cases ps with
    | nil => simp at hne
    | cons b qs =>
      have hp : (a::b::qs).Perm (a::(qs++[b])) :=
        List.Perm.cons a (by simpa using (List.perm_append_comm : ([b]++qs).Perm (qs++[b])))
      have hn' : (a::(qs++[b])).Nodup := hp.nodup_iff.mp hn
      have hall' : ∀ c, c∈a::(qs++[b]) := fun c => hp.mem_iff.mp (hall c)
      have hl := macro_XL a b qs H z hn h
      have hl' : Represents ((qs++[b]).length+1) (H+1) (a::(qs++[b])) (exchange a b z) := by
        simpa [run,step,swap,left,List.length_append,Nat.add_assoc] using hl
      obtain ⟨z',hz',hc⟩ := ih (qs++[b]) (H+1) (exchange a b z) (by simp) hall' hn' hl'
      refine ⟨z', ?_, ?_⟩
      · simpa [forward,run_append,run_U,left,Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using hz'
      · intro c
        have hs := macro_XL_logical a b qs H z hall hn h c
        have hc' := hc c
        simp only [List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one] at hc'
        rw [hs] at hc'
        by_cases he : c=a <;> simpa [he,List.length_cons,Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using hc'

/-- The word used above has the exact paid length, not merely a macro count. -/
theorem forward_transport_cost (k : Nat) : (forward k).length=2*k := forward_length k

/-- Explicit native endpoint: the buffer label is not changed or rotated away. -/
theorem forward_transport_endpoint (k : Nat) (a : α) (ps : List α) :
    run (forward k) (a::ps)=a::(left^[k]) ps := run_forward k a ps

#print axioms forward_transport
#print axioms forward_transport_cost
#print axioms forward_transport_endpoint
/-- Dual paid RX transport; arbitrary winding, no balanced-lift hypothesis. -/
theorem backward_transport (k : Nat) (a : α) (ps : List α) (H : Int) (z : α → Int)
    (hne : 1 ≤ ps.length) (hall : ∀ c, c∈a::ps) (hn : (a::ps).Nodup)
    (h : Represents (ps.length+1) H (a::ps) z) :
    ∃ z' : α → Int,
      Represents (ps.length+1) (H-(k:Int)) (run (backward k) (a::ps)) z' ∧
      ∀ c, contract (ps.length:Int) (H-(k:Int)) (z' c) =
        contract (ps.length:Int) H (z c)-(if c=a then (k:Int) else 0) := by
  induction k generalizing ps H z with
  | zero => exact ⟨z, by simpa [backward,run] using h, by intro c; simp⟩
  | succ k ih =>
    induction ps using List.reverseRecOn with
    | nil => simp at hne
    | append_singleton qs b unused =>
      have hp : (a::(qs++[b])).Perm (a::b::qs) :=
        List.Perm.cons a (by simpa using (List.perm_append_comm : (qs++[b]).Perm ([b]++qs)))
      have hn' : (a::b::qs).Nodup := hp.nodup_iff.mp hn
      have hall' : ∀ c, c∈a::b::qs := fun c => hp.mem_iff.mp (hall c)
      have h0 : Represents (qs.length+2) H ((a::qs)++[b]) z := by simpa using h
      have hl := macro_RX a b qs H z hn h0
      have hl' : Represents ((b::qs).length+1) (H-1) (a::b::qs) (exchange b a z) := by
        change Represents (qs.length+2) (H-1) (run V (a::(qs++[b]))) (exchange b a z) at hl
        rw [run_V, right_append] at hl
        simpa [Nat.add_assoc] using hl
      obtain ⟨z',hz',hc⟩ := ih (b::qs) (H-1) (exchange b a z) (by simp) hall' hn' hl'
      refine ⟨z', ?_, ?_⟩
      · simpa [backward,run_append,run_V,right_append,Nat.cast_add,Nat.cast_one,
          sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using hz'
      · intro c
        have hs := macro_RX_logical a b qs H z hall hn h0 c
        have hc' := hc c
        simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hc'
        rw [hs] at hc'
        by_cases he : c=a <;> simpa [he,List.length_append,Nat.cast_add,Nat.cast_one,
          sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using hc'

theorem backward_transport_cost (k : Nat) : (backward k).length=2*k := backward_length k

theorem backward_transport_endpoint (k : Nat) (a : α) (ps : List α) :
    run (backward k) (a::ps)=a::(right^[k]) ps := run_backward k a ps

#print axioms backward_transport
#print axioms backward_transport_cost
#print axioms backward_transport_endpoint
end LRX.UpperNativeLift
