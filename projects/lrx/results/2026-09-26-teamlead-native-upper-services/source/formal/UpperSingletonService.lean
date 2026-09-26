import UpperTargetStep

/-! Constructed singleton target-cycle service (including arbitrary winding).
This is the one-label base case, not arbitrary multi-label cycle existence. -/
namespace LRX.UpperNativeLift
open LRX.BlockExchange LRX.UpperAffineBuffer
variable {α : Type*} [DecidableEq α]

/-- Enter child a, transport it by M*w, return parent p. Every letter paid;
parent and all labels other than a keep their integer logical coordinates. -/
theorem paid_singleton_return (p a : α) (ps : List α) (H w : Int) (z : α → Int)
    (hall : ∀ c, c∈p::a::ps) (hn : (p::a::ps).Nodup)
    (h : Represents (ps.length+2) H (p::a::ps) z) :
    ∃ qs u, ps.length=qs.length ∧
      PaidEffect (ps.length+2) (p::a::ps) (p::a::qs)
        H (H+((ps.length:Int)+1)*w) z u
        ([.X]++signedTransport (((ps.length:Int)+1)*w)++[.X])
        (fun c => if c=a then ((ps.length:Int)+1)*w else 0)
        (2*(((ps.length:Int)+1)*w).natAbs+2) := by
  have hpa : p≠a := by
    intro he
    exact (List.nodup_cons.mp hn).1 (by simp [he])
  have he := paid_handoff p a ps H z hn h
  have hp : (p::a::ps).Perm (a::p::ps) := List.Perm.swap _ _ _
  have hn' := hp.nodup_iff.mp hn
  have hall' : ∀ c, c∈a::p::ps := fun c => hp.mem_iff.mp (hall c)
  obtain ⟨wa,hwa⟩ := buffer_logical_winding a (p::ps) (ps.length+2) H
    (exchange p a z) (by omega) he.represented
  have hm : ((ps.length+2:Nat):Int)-1=(ps.length:Int)+1 := by omega
  rw [hm] at hwa
  obtain ⟨wp,hwp⟩ := he.represented 1 (by simp)
  simp only [List.getElem_cons_succ,List.getElem_cons_zero,Nat.cast_one] at hwp
  have hpv : contract ((ps.length:Int)+1) H (exchange p a z p)=H+((ps.length:Int)+1)*wp := by
    rw [hwp]
    convert contract_native_positive ((ps.length:Int)+1) H 1 wp (by omega) (by omega) (by omega) using 1 <;> push_cast <;> ring_nf
  have ht : contract ((ps.length:Int)+1) H (exchange p a z p)=
      contract ((ps.length:Int)+1) H (exchange p a z a)+
        ((ps.length:Int)+1)*w+((ps.length:Int)+1)*(wp-wa-w) := by
    rw [hpv,hwa]; ring
  obtain ⟨qs,u,hlen,hs⟩ := signed_target_step (((ps.length:Int)+1)*w) a p (p::ps)
    H (wp-wa-w) (exchange p a z) (by simp) hall' hn'
    (by simpa only [List.length_cons,Nat.add_assoc] using he.represented) hpa
    (by simpa only [List.length_cons,Nat.cast_add,Nat.cast_one] using ht)
  have hs' : PaidEffect (ps.length+2) (a::p::ps) (p::a::qs) H
      (H+((ps.length:Int)+1)*w) (exchange p a z) u
      (signedTransport (((ps.length:Int)+1)*w)++[.X])
      (fun c => if c=a then ((ps.length:Int)+1)*w else 0)
      (2*(((ps.length:Int)+1)*w).natAbs+1) := by
    simpa only [List.length_cons,Nat.add_assoc] using hs
  refine ⟨qs,u,by simpa using hlen,?_⟩
  have hc : 1+(2*(((ps.length:Int)+1)*w).natAbs+1)=2*(((ps.length:Int)+1)*w).natAbs+2 := by omega
  have hfinal := he.append hs'
  rw [hc] at hfinal
  simpa only [List.append_assoc,zero_add] using hfinal

/-- The existing service interface is inhabited for an actual singleton cycle;
no PaidEffect/service existence is assumed. This does not cover longer cycles. -/
theorem singleton_service (p a : α) (ps : List α) (H w : Int) (z : α → Int)
    (hall : ∀ c, c∈p::a::ps) (hn : (p::a::ps).Nodup)
    (h : Represents (ps.length+2) H (p::a::ps) z) :
    ∃ qs u, SubtreeService (ps.length+2) ({()} : Finset Unit) (fun _ => w)
      {a} (fun _ => ((ps.length:Int)+1)*w) p (a::ps) (a::qs)
      H (H+((ps.length:Int)+1)*w) z u
      ([.X]++signedTransport (((ps.length:Int)+1)*w)++[.X])
      (2*(((ps.length:Int)+1)*w).natAbs+2) := by
  obtain ⟨qs,u,_,he⟩ := paid_singleton_return p a ps H w z hall hn h
  refine ⟨qs,u,?_,?_,?_⟩
  · simpa using he
  · simp; omega
  · simp only [Finset.mem_singleton]
    intro hpa
    exact (List.nodup_cons.mp hn).1 (by simp [hpa])

#print axioms paid_singleton_return
#print axioms singleton_service
end LRX.UpperNativeLift
