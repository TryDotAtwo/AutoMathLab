import UpperCyclePrefix

/-! Constructive two-label returning service; general cycle induction pending. -/
namespace LRX.UpperNativeLift
open LRX.BlockExchange LRX.UpperAffineBuffer
variable {α : Type*} [DecidableEq α]

/-- An actual two-label cycle, with entry and final return both paid.
Its one internal congruence and total winding imply the last handoff. -/
theorem paid_pair_return (p a b : α) (ps : List α) (H tau sigma w targetW : Int)
    (z : α → Int) (hall : ∀ c, c∈p::a::b::ps) (hn : (p::a::b::ps).Nodup)
    (h : Represents (ps.length+3) H (p::a::b::ps) z)
    (ht : contract ((ps.length:Int)+2) H (z b)=
      contract ((ps.length:Int)+2) H (z a)+tau+((ps.length:Int)+2)*targetW)
    (hw : tau+sigma=((ps.length:Int)+2)*w) :
    ∃ qs v, ps.length+1=qs.length ∧
      PaidEffect (ps.length+3) (p::a::b::ps) (p::b::qs)
        H (H+((ps.length:Int)+2)*w) z v
        ([.X]++(signedTransport tau++[.X])++(signedTransport sigma++[.X]))
        (fun c => (if c=a then tau else 0)+(if c=b then sigma else 0))
        (2*tau.natAbs+2*sigma.natAbs+3) := by
  have hpall := (List.nodup_cons.mp hn).1
  have hnab := (List.nodup_cons.mp hn).2
  have hab : b≠a := by
    intro he
    exact (List.nodup_cons.mp hnab).1 (by simp [he])
  have hpa : p≠a := by intro he; exact hpall (by simp [he])
  have hpb : p≠b := by intro he; exact hpall (by simp [he])
  have he := paid_handoff p a (b::ps) H z hn
    (by simpa only [List.length_cons,Nat.add_assoc] using h)
  have ht' : contract ((p::b::ps).length:Int) H (z b)=
      contract ((p::b::ps).length:Int) H (z a)+tau+
        ((p::b::ps).length:Int)*targetW := by
    simpa [List.length_cons,Nat.cast_add,add_assoc] using ht
  have he' : PaidEffect ((p::b::ps).length+1) (p::a::b::ps) (a::p::b::ps)
      H H z (exchange p a z) [.X] (fun _ => 0) 1 := by
    simpa only [List.length_cons,Nat.add_assoc] using he
  obtain ⟨ys,u,hlen,h1⟩ := he'.extend_fresh_target hall hn (by simp) b tau targetW hab rfl rfl ht'
  have hlen' : ps.length+1=ys.length := by simpa using hlen
  have h1' : PaidEffect ((a::ys).length+1) (p::a::b::ps) (b::a::ys) H (H+tau) z u
      ([.X]++(signedTransport tau++[.X]))
      (fun c => if c=a then tau else 0) (2*tau.natAbs+2) := by
    have heq : (a::ys).length+1=(p::b::ps).length+1 := by simp only [List.length_cons]; omega
    rw [heq]
    simp only [zero_add] at h1
    convert h1 using 1 <;> omega
  obtain ⟨wp,hwp⟩ := buffer_logical_winding p (a::b::ps) (ps.length+3) H z (by omega) h
  have hm : ((ps.length+3:Nat):Int)-1=(ps.length:Int)+2 := by omega
  rw [hm] at hwp
  have hM : ((a::ys).length:Int)=(ps.length:Int)+2 := by simp only [List.length_cons]; omega
  have hparent : contract ((a::ys).length:Int) H (z p)=H+((a::ys).length:Int)*wp := by
    simpa only [hM] using hwp
  have hframe : (H+tau)+sigma=H+((a::ys).length:Int)*w := by rw [hM]; omega
  obtain ⟨qs,v,hq,h2⟩ := h1'.close_parent hall hn (by simp) p sigma w wp hpb
    (by simp [hpa]) hparent hframe
  refine ⟨qs,v,?_,?_⟩
  · simp only [List.length_cons] at hq
    omega
  · have heq : (a::ys).length+1=ps.length+3 := by simp only [List.length_cons]; omega
    rw [heq,hM] at h2
    convert h2 using 1 <;> omega

#print axioms paid_pair_return
end LRX.UpperNativeLift
