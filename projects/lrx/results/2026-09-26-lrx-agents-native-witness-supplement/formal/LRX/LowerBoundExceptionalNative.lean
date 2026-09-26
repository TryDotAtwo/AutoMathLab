import LRX.LowerBoundExceptional
import LRX.LowerBoundExceptionalCount
import LRX.LowerBoundFourParity
import Mathlib.Data.Finset.Card

namespace LRX.LowerBoundExceptionalNative
open LRX.BlockExchange LRX.LowerBoundNoRepeat LRX.LowerBoundSwapCount
open LRX.LowerBoundExceptional LRX.LowerBoundExceptionalCount
open LRX.LowerBoundFourParity LRX.LowerBoundFoldedTransport LRX.LowerBoundPaidProjection
open LRX.Cycle11StructuralBridge
variable {α : Type*} [DecidableEq α] [Fintype α]

def colorClass (color : α → Bool) (c : Bool) : Finset α :=
  Finset.univ.filter (fun x => color x = c)

theorem other_class_card (color : α → Bool) (c : Bool) :
    (colorClass color c).card + (colorClass color (!c)).card = Fintype.card α := by
  have he : colorClass color (!c) = Finset.univ.filter (fun x => ¬color x=c) := by
    ext x
    cases hx : color x <;> cases c <;> simp [colorClass, hx]
  rw [he]
  exact Finset.card_filter_add_card_filter_not (fun x => color x=c)

theorem class_exchange_bound (color : α → Bool) (c : Bool)
    (w : List Op) (s : List α) (hs : s.Nodup) (hlen : 2≤s.length)
    (hc : ∀ a b : α, a≠b → swapCount a b w s=if color a=color b then 1 else 0) :
    (colorClass color c).card * ((colorClass color c).card-1) ≤ 2*exchanges w := by
  apply complete_subset_exchange_bound _ w s hs hlen
  intro a ha b hb hab
  have ha' : color a=c := (Finset.mem_filter.mp ha).2
  have hb' : color b=c := (Finset.mem_filter.mp hb).2
  simpa [ha', hb'] using hc a b hab

/-- Empty class: all unordered pairs are actually exchanged. No shortestness
or cursor normalization is required in this branch. -/
theorem empty_class_lower (color : α → Bool) (c : Bool)
    (w : List Op) (s : List α) (hs : s.Nodup) (hlen : 2≤s.length)
    (hc : ∀ a b : α, a≠b → swapCount a b w s=if color a=color b then 1 else 0)
    (hempty : (colorClass color c).card=0) :
    Fintype.card α * (Fintype.card α-1)/2 ≤ w.length := by
  have hn := other_class_card color c
  have hx := class_exchange_bound color (!c) w s hs hlen hc
  have hlen' := every_letter_charged w
  have he : (colorClass color (!c)).card=Fintype.card α := by omega
  rw [he] at hx
  omega

theorem singleton_arithmetic (n m r len : Nat) (hn : 5≤n)
    (hx : (n-1)*(n-2) ≤ 2*m) (hr : m≤r+1) (hl : r+m=len) :
    n*(n-1)/2 ≤ len := by
  have hn1 : n-1+1=n := by omega
  have hn2 : n-2+2=n := by omega
  have hn5 : n-5+5=n := by omega
  have hpoly := Nat.zero_le ((n-5)*(n-1))
  have hb : n*(n-1)≤2*len := by nlinarith
  omega

/-- Singleton case for n≥5, for either choice of the small color. -/
theorem singleton_class_lower_ge_five (color : α → Bool) (c : Bool)
    (w : List Op) (s : List α) (hs : s.Nodup) (hlen : 2≤s.length)
    (hn : 5≤Fintype.card α) (hmin : Shortest w s)
    (hc : ∀ a b : α, a≠b → swapCount a b w s=if color a=color b then 1 else 0)
    (hsingle : (colorClass color c).card=1) :
    Fintype.card α * (Fintype.card α-1)/2 ≤ w.length := by
  have hn' := other_class_card color c
  have he : (colorClass color (!c)).card=Fintype.card α-1 := by omega
  have hx := class_exchange_bound color (!c) w s hs hlen hc
  rw [he] at hx
  have hsub : Fintype.card α-1-1=Fintype.card α-2 := by omega
  rw [hsub] at hx
  exact singleton_arithmetic _ _ _ _ hn hx (shortest_exchange_budget w s hmin)
    (every_letter_charged w)

/-- At n=4, the singleton X budget gives length≥5; actual word parity
excludes length5 and supplies the missing unit. -/
theorem singleton_class_lower_four (color : α → Bool) (c : Bool)
    (w : List Op) (s : List α) (hs : s.Nodup) (hlen : 2≤s.length)
    (hn : Fintype.card α=4) (hmin : Shortest w s)
    (hc : ∀ a b : α, a≠b → swapCount a b w s=if color a=color b then 1 else 0)
    (hsingle : (colorClass color c).card=1) (heven : w.length%2=0) :
    6 ≤ w.length := by
  have hn' := other_class_card color c
  have he : (colorClass color (!c)).card=3 := by omega
  have hx := class_exchange_bound color (!c) w s hs hlen hc
  rw [he] at hx
  have hr := shortest_exchange_budget w s hmin
  have hl := every_letter_charged w
  omega

def root (n : Nat) : List (Fin n) := List.finRange n
def target (n : Nat) : List (Fin n) := (root n).reverse.rotate (n-2)

/-- Native exceptional branch, including both class orders. Its only
structural hypothesis is the exact pair-count conclusion already proved
in LowerBoundSwapCount; the n=4 parity is derived from the native endpoint. -/
theorem shortest_exceptional_native_lower {n : Nat} (hn : 4≤n)
    (w : List Op) (hmin : Shortest w (root n)) (hend : run w (root n)=target n)
    (color : Fin n → Bool) (c : Bool)
    (hc : ∀ a b : Fin n, a≠b →
      swapCount a b w (root n)=if color a=color b then 1 else 0)
    (hsmall : (colorClass color c).card≤1) : n*(n-1)/2≤w.length := by
  have hs : (root n).Nodup := List.nodup_finRange n
  have hlen : 2≤(root n).length := by simpa [root] using (show 2≤n by omega)
  by_cases hz : (colorClass color c).card=0
  · simpa using empty_class_lower color c w (root n) hs hlen hc hz
  · have ho : (colorClass color c).card=1 := by omega
    by_cases h4 : n=4
    · subst n
      have hp := four_fin_native_even w hend
      have hb := singleton_class_lower_four color c w (root 4) hs hlen
        (by simp) hmin hc ho hp
      norm_num at ⊢
      exact hb
    · simpa using singleton_class_lower_ge_five color c w (root n) hs hlen
        (by simpa using (show 5≤n by omega)) hmin hc ho

#print axioms empty_class_lower
#print axioms singleton_class_lower_ge_five
#print axioms singleton_class_lower_four
#print axioms shortest_exceptional_native_lower
end LRX.LowerBoundExceptionalNative
