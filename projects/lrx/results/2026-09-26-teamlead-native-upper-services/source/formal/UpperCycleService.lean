import UpperCyclePrefix

/-! Actual arbitrary finite cycle service. The route conditions are explicit
integer target congruences; no endpoint/service certificate is assumed. -/
namespace LRX.UpperNativeLift
open LRX.BlockExchange LRX.UpperAffineBuffer
variable {α : Type*} [DecidableEq α]

/-- Logical accumulated effect, retaining integer winding. -/
def cycleDelta (tau : α → Int) (labels : List α) (c : α) : Int :=
  (labels.map (fun a => if c=a then tau a else 0)).sum

def cycleCost (tau : α → Int) (labels : List α) : Nat :=
  (labels.map (fun a => 2*(tau a).natAbs+1)).sum

def cycleShift (tau : α → Int) (labels : List α) : Int :=
  (labels.map tau).sum

def cycleWord (tau : α → Int) (labels : List α) : List Op :=
  labels.flatMap (fun a => signedTransport (tau a)++[.X])

/-- Adjacent target congruences, with no restriction to zero winding. -/
def TargetChain (M : Int) (y tau : α → Int) : List α → Prop
  | [] => True
  | [_] => True
  | a::b::rest => (∃ w : Int, y b=y a+tau a+M*w) ∧ TargetChain M y tau (b::rest)

/-- Fixed-n wrapper: construct an edge from the current real prefix. -/
theorem PaidEffect.extend_fixed {n : Nat} {xs : List α} {a : α} {ps : List α}
    {H K : Int} {z u : α → Int} {word : List Op} {delta : α → Int} {cost : Nat}
    (h : PaidEffect n xs (a::ps) H K z u word delta cost)
    (hlen : n=ps.length+1) (hsize : 2≤n)
    (hall : ∀ c, c∈xs) (hn : xs.Nodup)
    (b : α) (t w : Int) (hba : b≠a) (ha : delta a=0) (hb : delta b=0)
    (ht : contract ((n:Int)-1) H (z b)=contract ((n:Int)-1) H (z a)+t+((n:Int)-1)*w) :
    ∃ qs v, n=qs.length+1 ∧
      PaidEffect n xs (b::qs) H (K+t) z v
        (word++(signedTransport t++[.X]))
        (fun c => delta c+(if c=a then t else 0)) (cost+(2*t.natAbs+1)) := by
  subst n
  have hm : ((ps.length+1:Nat):Int)-1=(ps.length:Int) := by omega
  rw [hm] at ht
  obtain ⟨qs,v,hlen,he⟩ := h.extend_fresh_target hall hn (by omega) b t w hba ha hb ht
  exact ⟨a::qs,v,by simp only [List.length_cons]; omega,he⟩

/-- Fixed-n wrapper for the final paid return. -/
theorem PaidEffect.close_fixed {n : Nat} {xs : List α} {a : α} {ps : List α}
    {H K : Int} {z u : α → Int} {word : List Op} {delta : α → Int} {cost : Nat}
    (h : PaidEffect n xs (a::ps) H K z u word delta cost)
    (hlen : n=ps.length+1) (hsize : 2≤n)
    (hall : ∀ c, c∈xs) (hn : xs.Nodup)
    (p : α) (t w wp : Int) (hpa : p≠a) (hp : delta p=0)
    (hparent : contract ((n:Int)-1) H (z p)=H+((n:Int)-1)*wp)
    (hframe : K+t=H+((n:Int)-1)*w) :
    ∃ qs v, n=qs.length+1 ∧
      PaidEffect n xs (p::qs) H (H+((n:Int)-1)*w) z v
        (word++(signedTransport t++[.X]))
        (fun c => delta c+(if c=a then t else 0)) (cost+(2*t.natAbs+1)) := by
  subst n
  have hm : ((ps.length+1:Nat):Int)-1=(ps.length:Int) := by omega
  rw [hm] at hparent hframe ⊢
  obtain ⟨qs,v,hlen,he⟩ := h.close_parent hall hn (by omega) p t w wp hpa hp hparent hframe
  exact ⟨a::qs,v,by simp only [List.length_cons]; omega,he⟩

/-- Finish any fresh Nodup target list from an already constructed prefix.
The inductive step constructs an actual signed native transport and paid X;
the last step constructs the return to the untouched parent. -/
theorem PaidEffect.finish_cycle {n : Nat} {xs : List α} (p : α)
    (tau : α → Int) (rest : List α)
    {H : Int} {z : α → Int} (w wp : Int)
    (hsize : 2≤n) (hall : ∀ c, c∈xs) (hn : xs.Nodup)
    (hparent : contract ((n:Int)-1) H (z p)=H+((n:Int)-1)*wp) :
    ∀ (a : α) (ps : List α) (K : Int) (u : α → Int) (word : List Op)
      (delta : α → Int) (cost : Nat),
      n=ps.length+1 →
      PaidEffect n xs (a::ps) H K z u word delta cost →
      (p::a::rest).Nodup → delta p=0 →
      (∀ c∈a::rest, delta c=0) →
      TargetChain ((n:Int)-1) (fun c => contract ((n:Int)-1) H (z c)) tau (a::rest) →
      K+cycleShift tau (a::rest)=H+((n:Int)-1)*w →
      ∃ qs v, n=qs.length+1 ∧
        PaidEffect n xs (p::qs) H (H+((n:Int)-1)*w) z v
          (word++cycleWord tau (a::rest))
          (fun c => delta c+cycleDelta tau (a::rest) c)
          (cost+cycleCost tau (a::rest)) := by
  induction rest with
  | nil =>
    intro a ps K u word delta cost hlen h hnd hp hf ht hframe
    have hpa : p≠a := by
      intro he
      exact (List.nodup_cons.mp hnd).1 (by simp [he])
    obtain ⟨qs,v,hq,he⟩ := h.close_fixed hlen hsize hall hn p (tau a) w wp hpa hp hparent
      (by simpa [cycleShift] using hframe)
    exact ⟨qs,v,hq,by simpa [cycleWord,cycleDelta,cycleCost] using he⟩
  | cons b rest ih =>
    intro a ps K u word delta cost hlen h hnd hp hf ht hframe
    have hna := (List.nodup_cons.mp hnd).2
    have hab : b≠a := by
      intro he
      exact (List.nodup_cons.mp hna).1 (by simp [he])
    obtain ⟨⟨edgeW,hedge⟩,htail⟩ := ht
    obtain ⟨ys,v,hy,he⟩ := h.extend_fixed hlen hsize hall hn b (tau a) edgeW hab
      (hf a (by simp)) (hf b (by simp)) hedge
    have hnd' : (p::b::rest).Nodup := by
      exact List.Nodup.sublist (by simp) hnd
    have hpa : p≠a := by
      intro heq
      exact (List.nodup_cons.mp hnd).1 (by simp [heq])
    have hp' : delta p+(if p=a then tau a else 0)=0 := by simp [hp,hpa]
    have hf' : ∀ c∈b::rest, delta c+(if c=a then tau a else 0)=0 := by
      intro c hc
      have hca : c≠a := by
        intro heq
        exact (List.nodup_cons.mp hna).1 (by simpa [heq] using hc)
      simp [hf c (List.mem_cons_of_mem a hc),hca]
    obtain ⟨qs,v',hq,hout⟩ := ih b ys (K+tau a) v
      (word++(signedTransport (tau a)++[.X]))
      (fun c => delta c+(if c=a then tau a else 0)) (cost+(2*(tau a).natAbs+1))
      hy he hnd' hp' hf' htail (by simpa [cycleShift,add_assoc] using hframe)
    refine ⟨qs,v',hq,?_⟩
    simpa [cycleWord,cycleDelta,cycleCost,List.append_assoc,add_assoc] using hout


/-- Full service for an arbitrary nonempty cycle in arbitrary passive positions.
Only its first label is adjacent to the parent at entry. The route is supplied
as target congruences and total winding, NOT as a native word certificate. -/
theorem paid_cycle_return (p a : α) (ps rest : List α) (H w : Int)
    (z tau : α → Int)
    (hall : ∀ c, c∈p::a::ps) (hn : (p::a::ps).Nodup)
    (h : Represents (ps.length+2) H (p::a::ps) z)
    (hlabels : (p::a::rest).Nodup)
    (ht : TargetChain ((ps.length:Int)+1)
      (fun c => contract ((ps.length:Int)+1) H (z c)) tau (a::rest))
    (hw : cycleShift tau (a::rest)=((ps.length:Int)+1)*w) :
    ∃ qs v, ps.length+1=qs.length ∧
      PaidEffect (ps.length+2) (p::a::ps) (p::qs)
        H (H+((ps.length:Int)+1)*w) z v
        ([.X]++cycleWord tau (a::rest)) (cycleDelta tau (a::rest))
        (1+cycleCost tau (a::rest)) := by
  have he := paid_handoff p a ps H z hn h
  obtain ⟨wp,hwp⟩ := buffer_logical_winding p (a::ps) (ps.length+2) H z (by omega) h
  have hm : ((ps.length+2:Nat):Int)-1=(ps.length:Int)+1 := by omega
  obtain ⟨qs,v,hq,hout⟩ := PaidEffect.finish_cycle p tau rest w wp
    (by omega : 2≤ps.length+2) hall hn hwp
    a (p::ps) H (exchange p a z) [.X] (fun _ => 0) 1
    (by simp) he hlabels rfl (by simp)
    (by simpa only [hm] using ht) (by rw [hm,hw])
  refine ⟨qs,v,by omega,?_⟩
  simpa only [hm,zero_add] using hout

/-- For a distinct cycle, each selected label receives exactly its prescribed
shift; all other labels receive zero, including the parent. -/
theorem cycleDelta_eq (tau : α → Int) (labels : List α) (hn : labels.Nodup) (c : α) :
    cycleDelta tau labels c = if c∈labels then tau c else 0 := by
  induction labels with
  | nil => simp [cycleDelta]
  | cons a rest ih =>
    have hnr := (List.nodup_cons.mp hn).2
    have hnot := (List.nodup_cons.mp hn).1
    by_cases hca : c=a
    · subst c
      have hi := ih hnr
      simp only [if_neg hnot,cycleDelta] at hi
      simp [cycleDelta,hi]
    · have hi := ih hnr
      simpa [cycleDelta,hca] using hi

/-- Every edge has its paid handoff, and entry contributes one additional X. -/
theorem cycleCost_eq (tau : α → Int) (labels : List α) :
    cycleCost tau labels = 2*(labels.map (fun a => (tau a).natAbs)).sum+labels.length := by
  induction labels with
  | nil => simp [cycleCost]
  | cons a rest ih =>
    simp only [cycleCost,List.map_cons,List.sum_cons] at ih ⊢
    rw [ih]
    simp only [List.length_cons]
    omega

/-- Constructed inhabitant of the returning-service interface for one complete
cycle, preserving all its labels and arbitrary winding. -/
theorem cycle_service (p a : α) (ps rest : List α) (H w : Int)
    (z tau : α → Int)
    (hall : ∀ c, c∈p::a::ps) (hn : (p::a::ps).Nodup)
    (h : Represents (ps.length+2) H (p::a::ps) z)
    (hlabels : (p::a::rest).Nodup)
    (ht : TargetChain ((ps.length:Int)+1)
      (fun c => contract ((ps.length:Int)+1) H (z c)) tau (a::rest))
    (hw : cycleShift tau (a::rest)=((ps.length:Int)+1)*w) :
    ∃ qs v, SubtreeService (ps.length+2) ({()} : Finset Unit) (fun _ => w)
      (a::rest).toFinset tau p (a::ps) qs H (H+((ps.length:Int)+1)*w) z v
      ([.X]++cycleWord tau (a::rest)) (1+cycleCost tau (a::rest)) := by
  obtain ⟨qs,v,_,he⟩ := paid_cycle_return p a ps rest H w z tau hall hn h hlabels ht hw
  refine ⟨qs,v,?_,?_,?_⟩
  · have hd : cycleDelta tau (a::rest) =
        (fun c => if c∈(a::rest).toFinset then tau c else 0) := by
      funext c
      simpa using cycleDelta_eq tau (a::rest) (List.nodup_cons.mp hlabels).2 c
    rw [hd] at he
    exact he
  · simp; omega
  · simpa using (List.nodup_cons.mp hlabels).1

#print axioms paid_cycle_return
#print axioms cycleDelta_eq
#print axioms cycleCost_eq
#print axioms cycle_service
#print axioms PaidEffect.extend_fixed
#print axioms PaidEffect.close_fixed
#print axioms PaidEffect.finish_cycle
end LRX.UpperNativeLift
