import LRX.Cycle11BlockReversal
import LRX.Cycle11WordSymmetry
import LRX.LowerBoundNativeComplete

/-! The historical reflection witness, report of 2026-09-16, section 6
(Astra Ultra <3, message 1268). The interval word zig, its exact endpoint,
and length were formalized by A in Cycle11BlockReversal. B adds only the
balanced two-block composition, paid transfer, and final two R letters.
This constructs an upper bound for ONE specified pair, not all vertices. -/
namespace LRX.ReflectionWitness
open LRX.BlockExchange LRX.ReducedPrice LRX.Cycle11BlockReversal
open LRX.Cycle11WordSymmetry LRX.LowerBoundExceptionalNative

variable {α : Type*}

def transfer (a b : Nat) : Int :=
  if offset a=offset b then (a : Int) else -(a : Int)

def word (n : Nat) : List Op :=
  let a := n/2
  let b := n-a
  zig a ++ spin (transfer a b) ++ inverse (zig b) ++ [.R,.R]

theorem transfer_length (a b : Nat) : (spin (transfer a b)).length=a := by
  rw [spin_length]
  unfold transfer
  split_ifs <;> simp

theorem inverse_length (w : List Op) : (inverse w).length=w.length := by
  simp [inverse, mirror]

theorem full_spin (s : List α) : run (spin (s.length : Int)) s=s := by
  simpa using spin_prefix s []

theorem spin_add_period (k : Int) (s : List α) :
    run (spin (k+(s.length : Int))) s=run (spin k) s := by
  rw [add_comm k, spin_add, full_spin]

theorem transfer_cursor (a b : Nat) (ha : 2≤a) (hab : a≤b) (hba : b≤a+1) :
    (offset a : Int)+transfer a b=(a : Int)+offset b ∨
    (offset a : Int)+transfer a b+((a : Int)+b)=(a : Int)+offset b := by
  have hoa := offset_formula a ha
  have hob := offset_formula b (by omega)
  by_cases he : offset a=offset b
  · left; simp [transfer,he]; omega
  · right
    have hb : b=a+1 := by omega
    have ho : offset b=offset a+1 := by omega
    simp only [transfer,he,ite_false]
    omega

/-- The shorter transfer has cost a, including the odd-n wrap case. -/
theorem transfer_run (a b : Nat) (ha : 2≤a) (hab : a≤b) (hba : b≤a+1)
    (p q : List α) (hp : p.length=a) (hq : q.length=b) :
    run (spin (transfer a b)) (run (spin (offset a : Int)) (p.reverse++q)) =
      run (spin (offset b : Int)) (q++p.reverse) := by
  rw [← spin_add]
  have hs : (p.reverse++q).length=a+b := by simp [hp,hq]
  have hturn : run (spin (a : Int)) (p.reverse++q)=q++p.reverse := by
    simpa [hp] using spin_prefix p.reverse q
  have hh : run (spin ((offset a : Int)+transfer a b)) (p.reverse++q)=
      run (spin ((a : Int)+offset b)) (p.reverse++q) := by
    rcases transfer_cursor a b ha hab hba with he | he
    · rw [he]
    · rw [← he]
      have hz := spin_add_period ((offset a : Int)+transfer a b) (p.reverse++q)
      simpa [hs] using hz.symm
  rw [hh, spin_add, hturn]

theorem inverse_zig_run (b : Nat) (q rest : List α) (hq : q.length=b) :
    run (inverse (zig b)) (run (spin (offset b : Int)) (q++rest))=q.reverse++rest := by
  have h := zig_run b q.reverse rest (by simpa using hq)
  simp only [List.reverse_reverse] at h
  rw [← h]
  exact run_inverse (zig b) (q.reverse++rest)

/-- Exact native endpoint; the final RR is part of the actual word. -/
theorem two_block_endpoint (a b : Nat) (ha : 2≤a) (hab : a≤b) (hba : b≤a+1)
    (p q : List α) (hp : p.length=a) (hq : q.length=b) :
    run (zig a ++ spin (transfer a b) ++ inverse (zig b) ++ [.R,.R]) (p++q)=
      reflect (p++q) := by
  rw [run_append,run_append,run_append,zig_run a p q hp,
    transfer_run a b ha hab hba p q hp hq,inverse_zig_run b q p.reverse hq]
  rw [reflect_as_reverse, List.reverse_append]
  rfl

theorem word_length {n : Nat} (hn : 4≤n) : (word n).length=n*(n-1)/2 := by
  have ha : 2≤n/2 := by omega
  have hab : n/2≤n-n/2 := by omega
  have hba : n-n/2≤n/2+1 := by omega
  have h1 := zig_length (n/2) ha
  have h2 := zig_length (n-n/2) (by omega)
  have h3 := half_budget (n/2) (n-n/2) ha hab hba
  simp only [word,List.length_append,transfer_length,inverse_length,
    List.length_cons,List.length_nil]
  have he : n-n/2+n/2=n := by omega
  rw [he] at h3
  omega

theorem word_endpoint {n : Nat} (hn : 4≤n) : run (word n) (root n)=target n := by
  let p := (root n).take (n/2)
  let q := (root n).drop (n/2)
  have hp : p.length=n/2 := by simp [p,root]; omega
  have hq : q.length=n-n/2 := by simp [q,root]
  have hpq : p++q=root n := List.take_append_drop (n/2) (root n)
  have h := two_block_endpoint (n/2) (n-n/2) (by omega) (by omega) (by omega) p q hp hq
  rw [hpq] at h
  change run (word n) (root n)=reflect (root n) at h
  rw [h]
  simpa [target,root] using LRX.LowerBoundNativeComplete.reflect_eq_reverse_rotate
    (root n) (by simp [root]; omega)

#print axioms two_block_endpoint
#print axioms word_length
#print axioms word_endpoint
end LRX.ReflectionWitness
