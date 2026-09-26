import UpperRecursiveService

/-! Validity-preserving insertion of fully accounted returning descendants.
No native service certificate is an input; ServiceTree.realize supplies it.
Valid-tree selection from graph reachability is still outside this module. -/
namespace LRX.UpperNativeLift
open LRX.BlockExchange LRX.UpperAffineBuffer
variable {α : Type*} [DecidableEq α]

/-- All labels inspected by a recursive tree, including every descendant. -/
def ServiceTree.labels : ServiceTree α → Finset α
  | .edge a b _ => {a,b}
  | .seq s t => s.labels ∪ t.labels

/-- Change coordinates outside all the inspected labels without changing
geometric validity. Recursive right coordinates include all left effects. -/
theorem ServiceTree.valid_congr (tree : ServiceTree α) (M : Int) :
    ∀ (y y' : α → Int) (incoming : α),
      (∀ c∈tree.labels, y' c=y c) →
      tree.Valid M y incoming → tree.Valid M y' incoming := by
  induction tree with
  | edge a b t =>
    intro y y' incoming he hv
    obtain ⟨ha,hba,w,hw⟩ := hv
    refine ⟨ha,hba,w,?_⟩
    rw [he b (by simp [labels]),he a (by simp [labels])]
    exact hw
  | seq s t ihs iht =>
    intro y y' incoming he hv
    obtain ⟨hs,ht⟩ := hv
    refine ⟨ihs y y' incoming (fun c hc => he c (by simp [labels,hc])) hs,?_⟩
    apply iht (fun c => y c+s.delta c) (fun c => y' c+s.delta c) s.last
    · intro c hc
      rw [he c (by simp [labels,hc])]
    · exact ht

/-- Any complete returning child whose effect vanishes on the parent's
inspected labels can be inserted before that parent. Nonzero child winding
is allowed; no zero-head-shift assumption is made. -/
theorem ServiceTree.insert_valid (child parent : ServiceTree α) (M : Int)
    (y : α → Int) (a : α)
    (hc : child.Valid M y a) (hp : parent.Valid M y a)
    (hreturn : child.last=a)
    (hdisjoint : ∀ c∈parent.labels, child.delta c=0) :
    (ServiceTree.seq child parent).Valid M y a := by
  refine ⟨hc,?_⟩
  rw [hreturn]
  apply parent.valid_congr M y (fun c => y c+child.delta c) a
  · intro c hm
    simp [hdisjoint c hm]
  · exact hp

/-- Constructive insertion result: all child and parent letters are paid;
child winding is included in the final frame, never silently reset. -/
theorem ServiceTree.insert_realize (child parent : ServiceTree α)
    (n : Nat) (a : α) (ps : List α) (H : Int) (z : α → Int)
    (hlen : n=ps.length+1) (hsize : 2≤n)
    (hall : ∀ c, c∈a::ps) (hn : (a::ps).Nodup) (hr : Represents n H (a::ps) z)
    (hc : child.Valid ((n:Int)-1) (fun c => contract ((n:Int)-1) H (z c)) a)
    (hp : parent.Valid ((n:Int)-1) (fun c => contract ((n:Int)-1) H (z c)) a)
    (hreturn : child.last=a)
    (hdisjoint : ∀ c∈parent.labels, child.delta c=0) :
    ∃ qs v, n=qs.length+1 ∧
      PaidEffect n (a::ps) (parent.last::qs) H (H+(child.shift+parent.shift)) z v
        (child.word++parent.word) (fun c => child.delta c+parent.delta c)
        (child.cost+parent.cost) := by
  exact (ServiceTree.seq child parent).realize n a ps H z hlen hsize hall hn hr
    (child.insert_valid parent ((n:Int)-1) _ a hc hp hreturn hdisjoint)

/-- Labels outside a tree have exactly zero effect, even with repeated visits. -/
theorem ServiceTree.delta_outside (tree : ServiceTree α) (c : α)
    (hc : c∉tree.labels) : tree.delta c=0 := by
  induction tree with
  | edge a b t =>
    have hca : c≠a := by intro he; subst c; exact hc (by simp [labels])
    simp [delta,hca]
  | seq s t ihs iht =>
    have hcs : c∉s.labels := by intro hm; exact hc (by simp [labels,hm])
    have hct : c∉t.labels := by intro hm; exact hc (by simp [labels,hm])
    simp [delta,ihs hcs,iht hct]

#print axioms ServiceTree.valid_congr
#print axioms ServiceTree.insert_valid
#print axioms ServiceTree.insert_realize
#print axioms ServiceTree.delta_outside
end LRX.UpperNativeLift
