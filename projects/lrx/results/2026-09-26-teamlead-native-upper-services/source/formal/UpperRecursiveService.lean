import UpperCycleService

/-! Recursive paid native service compiler. All descendant nodes are retained.
Geometric validity is an explicit integer-coordinate predicate, not a supplied
native endpoint or service-existence hypothesis. Universal valid-plan selection
and the diameter budget are NOT established here. -/
namespace LRX.UpperNativeLift
open LRX.BlockExchange LRX.UpperAffineBuffer
variable {α : Type*} [DecidableEq α]

/-- A finite binary service syntax, allowing arbitrary nesting of subservices.
Each leaf is signed transport of the current label followed by a paid X. -/
inductive ServiceTree (α : Type*) where
  | edge (source target : α) (shift : Int)
  | seq (left right : ServiceTree α)

def ServiceTree.last : ServiceTree α → α
  | .edge _ b _ => b
  | .seq _ t => t.last

def ServiceTree.word : ServiceTree α → List Op
  | .edge _ _ t => signedTransport t++[.X]
  | .seq s t => s.word++t.word

def ServiceTree.shift : ServiceTree α → Int
  | .edge _ _ t => t
  | .seq s t => s.shift+t.shift

def ServiceTree.cost : ServiceTree α → Nat
  | .edge _ _ t => 2*t.natAbs+1
  | .seq s t => s.cost+t.cost

def ServiceTree.delta : ServiceTree α → α → Int
  | .edge a _ t => fun c => if c=a then t else 0
  | .seq s t => fun c => s.delta c+t.delta c

/-- Every node is checked, including zero-shift handoffs and descendants.
The right subtree sees the effects of ALL nodes in the left subtree. -/
def ServiceTree.Valid (M : Int) (y : α → Int) (incoming : α) : ServiceTree α → Prop
  | .edge a b t => a=incoming ∧ b≠a ∧ ∃ w : Int, y b=y a+t+M*w
  | .seq s t => s.Valid M y incoming ∧
      t.Valid M (fun c => y c+s.delta c) s.last

/-- A literal empty word is an actual zero-effect native prefix. -/
theorem paid_empty {n : Nat} (a : α) (ps : List α) (H : Int) (z : α → Int)
    (h : Represents n H (a::ps) z) :
    PaidEffect n (a::ps) (a::ps) H H z z [] (fun _ => 0) 0 := by
  exact ⟨rfl,h,by intro c; simp,rfl⟩

/-- Construct a real native word for every geometrically valid finite tree.
This is structural induction on the entire tree, not certificate composition
with uninhabited child-service assumptions. -/
theorem ServiceTree.realize (tree : ServiceTree α) :
    ∀ (n : Nat) (a : α) (ps : List α) (H : Int) (z : α → Int),
      n=ps.length+1 → 2≤n →
      (∀ c, c∈a::ps) → (a::ps).Nodup → Represents n H (a::ps) z →
      tree.Valid ((n:Int)-1) (fun c => contract ((n:Int)-1) H (z c)) a →
      ∃ qs v, n=qs.length+1 ∧
        PaidEffect n (a::ps) (tree.last::qs) H (H+tree.shift) z v
          tree.word tree.delta tree.cost := by
  induction tree with
  | edge src target t =>
    intro n a ps H z hlen hsize hall hn hr hv
    obtain ⟨hsrc,hba,w,ht⟩ := hv
    subst src
    obtain ⟨qs,v,hq,he⟩ := (paid_empty a ps H z hr).extend_fixed hlen hsize hall hn
      target t w hba rfl rfl ht
    exact ⟨qs,v,hq,by simpa [word,last,shift,delta,cost] using he⟩
  | seq s t ihs iht =>
    intro n a ps H z hlen hsize hall hn hr hv
    obtain ⟨hvs,hvt⟩ := hv
    obtain ⟨ys,u,hy,hs⟩ := ihs n a ps H z hlen hsize hall hn hr hvs
    have hall' : ∀ c, c∈s.last::ys := fun c => hs.perm.mem_iff.mp (hall c)
    have hn' : (s.last::ys).Nodup := hs.perm.nodup_iff.mp hn
    have hcoords : (fun c => contract ((n:Int)-1) (H+s.shift) (u c)) =
        (fun c => contract ((n:Int)-1) H (z c)+s.delta c) := by
      funext c
      exact hs.logical c
    have hvt' : t.Valid ((n:Int)-1)
        (fun c => contract ((n:Int)-1) (H+s.shift) (u c)) s.last := by
      rw [hcoords]
      exact hvt
    obtain ⟨qs,v,hq,ht⟩ := iht n s.last ys (H+s.shift) u hy hsize hall' hn'
      hs.represented hvt'
    exact ⟨qs,v,hq,by simpa [word,last,shift,delta,cost,add_assoc] using hs.append ht⟩

/-- A returning recursively nested plan inhabits SubtreeService once its
explicit arithmetic validator, winding and supported-effect equations hold.
The finite set cycles must account for every descendant; this theorem does
not construct that combinatorial bookkeeping or select a valid plan. -/
theorem ServiceTree.returning_service {κ : Type*} (tree : ServiceTree α)
    (n : Nat) (p : α) (ps : List α) (H : Int) (z : α → Int)
    (cycles : Finset κ) (winding : κ → Int) (labels : Finset α) (tau : α → Int)
    (hlen : n=ps.length+1) (hsize : 2≤n)
    (hall : ∀ c, c∈p::ps) (hn : (p::ps).Nodup) (hr : Represents n H (p::ps) z)
    (hv : tree.Valid ((n:Int)-1) (fun c => contract ((n:Int)-1) H (z c)) p)
    (hreturn : tree.last=p)
    (hshift : tree.shift=((n:Int)-1)*(∑ c∈cycles, winding c))
    (hdelta : tree.delta=fun c => if c∈labels then tau c else 0)
    (hp : p∉labels) :
    ∃ qs v, SubtreeService n cycles winding labels tau p ps qs H
      (H+((n:Int)-1)*(∑ c∈cycles, winding c)) z v tree.word tree.cost := by
  obtain ⟨qs,v,_,he⟩ := tree.realize n p ps H z hlen hsize hall hn hr hv
  rw [hreturn,hshift,hdelta] at he
  exact ⟨qs,v,he,rfl,hp⟩

#print axioms paid_empty
#print axioms ServiceTree.realize
#print axioms ServiceTree.returning_service
end LRX.UpperNativeLift
