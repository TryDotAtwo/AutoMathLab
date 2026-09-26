import UpperHeadPort

/-! A target-cycle edge implies actual native readiness after transport.
The transport certificate and target relation are explicit hypotheses;
this is not recursive service existence or a universal upper bound. -/
namespace LRX.UpperNativeLift
open LRX.BlockExchange
open LRX.UpperAffineBuffer
variable {α : Type*} [DecidableEq α]

/-- The current buffer's contracted position differs from H by an integer
multiple of n-1. The winding is not assumed zero. -/
theorem buffer_logical_winding (a : α) (qs : List α) (n : Nat)
    (H : Int) (z : α → Int) (hn : 2≤n)
    (h : Represents n H (a::qs) z) :
    ∃ w : Int, contract ((n:Int)-1) H (z a)=H+((n:Int)-1)*w := by
  obtain ⟨w,hw⟩ := h 0 (by simp)
  simp only [List.getElem_cons_zero,Nat.cast_zero,add_zero] at hw
  refine ⟨w,?_⟩
  rw [hw]
  convert contract_native_zero ((n:Int)-1) H w (by omega) using 1 <;> ring

/-- Target adjacency is an integer lift of the cycle congruence. A passive
next label remains at its original logical position; descendant frame shifts
by multiples of n-1 do not change readiness. No positivity condition on tau. -/
theorem target_edge_ready (a c : α) (qs ys : List α) (n : Nat)
    (H K tau targetW childW : Int) (z u : α → Int)
    (word : List Op) (delta : α → Int) (cost : Nat)
    (hn : 2≤n) (h : Represents n H (a::qs) z)
    (paid : PaidEffect n (a::qs) ys H K z u word delta cost)
    (hpassive : delta c=0)
    (hframe : K=H+tau+((n:Int)-1)*childW)
    (htarget : contract ((n:Int)-1) H (z c)=
      contract ((n:Int)-1) H (z a)+tau+((n:Int)-1)*targetW) :
    (contract ((n:Int)-1) K (u c)-K)%((n:Int)-1)=0 := by
  obtain ⟨w,hw⟩ := buffer_logical_winding a qs n H z hn h
  have hc := paid.outside c hpassive
  rw [hc,htarget,hw,hframe]
  have he : H+((n:Int)-1)*w+tau+((n:Int)-1)*targetW-
      (H+tau+((n:Int)-1)*childW)=((n:Int)-1)*(w+targetW-childW) := by ring
  rw [he,Int.mul_emod_right]

/-- The next label in a target edge becomes the actual new native buffer,
with one additional paid X and unchanged total logical effect. Includes
zero transport and arbitrary total descendant winding. -/
theorem paid_target_handoff (a b c : α) (qs ps : List α)
    (H K tau targetW childW : Int) (z u : α → Int)
    (word : List Op) (delta : α → Int) (cost : Nat)
    (h : Represents (ps.length+2) H (a::qs) z)
    (paid : PaidEffect (ps.length+2) (a::qs) (a::b::ps) H K z u word delta cost)
    (hn : (a::b::ps).Nodup) (hc : c∈a::b::ps) (hca : c≠a)
    (hpassive : delta c=0)
    (hframe : K=H+tau+((ps.length:Int)+1)*childW)
    (htarget : contract ((ps.length:Int)+1) H (z c)=
      contract ((ps.length:Int)+1) H (z a)+tau+((ps.length:Int)+1)*targetW) :
    PaidEffect (ps.length+2) (a::qs) (c::a::ps) H K z
      (exchange a c u) (word++[.X]) delta (cost+1) := by
  have hm : ((ps.length+2:Nat):Int)-1=(ps.length:Int)+1 := by omega
  have hr := target_edge_ready a c qs (a::b::ps) (ps.length+2)
    H K tau targetW childW z u word delta cost (by omega) h paid hpassive
    (by rw [hm]; exact hframe) (by rw [hm]; exact htarget)
  rw [hm] at hr
  have hx := paid_ready_handoff a b ps K u hn paid.represented c hc hca hr
  have hh := paid.append hx
  simpa only [add_zero] using hh

/-- Signed constructive transport, with every macro's two native moves paid. -/
def signedTransport : Int → List Op
  | .ofNat k => LRX.UpperBufferNative.forward k
  | .negSucc k => LRX.UpperBufferNative.backward (k+1)

theorem paid_signed (tau : Int) (a : α) (ps : List α) (H : Int) (z : α → Int)
    (hne : 1≤ps.length) (hall : ∀ c, c∈a::ps) (hn : (a::ps).Nodup)
    (h : Represents (ps.length+1) H (a::ps) z) :
    ∃ u, PaidEffect (ps.length+1) (a::ps)
      (run (signedTransport tau) (a::ps)) H (H+tau) z u
      (signedTransport tau) (fun c => if c=a then tau else 0) (2*tau.natAbs) := by
  cases tau with
  | ofNat k => simpa [signedTransport] using paid_forward k a ps H z hne hall hn h
  | negSucc k =>
    obtain ⟨u,hu⟩ := paid_backward (k+1) a ps H z hne hall hn h
    refine ⟨u,?_⟩
    have hd : (fun c : α => if c=a then Int.negSucc k else 0)=
        (fun c => -(if c=a then ((k+1:Nat):Int) else 0)) := by
      funext c
      by_cases ha : c=a
      · simp only [ha,if_pos]; omega
      · simp [ha]
    simp only [signedTransport,Int.natAbs_negSucc]
    rw [hd]
    convert hu using 1 <;> omega

/-- Nonvacuous target readiness: the transport certificate is constructed,
not assumed. tau=0 is included and executes the empty word at exact cost0. -/
theorem signed_target_ready (tau : Int) (a c : α) (ps : List α)
    (H targetW : Int) (z : α → Int)
    (hne : 1≤ps.length) (hall : ∀ c, c∈a::ps) (hn : (a::ps).Nodup)
    (h : Represents (ps.length+1) H (a::ps) z) (hca : c≠a)
    (htarget : contract (ps.length:Int) H (z c)=
      contract (ps.length:Int) H (z a)+tau+(ps.length:Int)*targetW) :
    ∃ u, PaidEffect (ps.length+1) (a::ps)
      (run (signedTransport tau) (a::ps)) H (H+tau) z u
      (signedTransport tau) (fun d => if d=a then tau else 0) (2*tau.natAbs) ∧
      (contract (ps.length:Int) (H+tau) (u c)-(H+tau))%(ps.length:Int)=0 := by
  obtain ⟨u,hu⟩ := paid_signed tau a ps H z hne hall hn h
  refine ⟨u,hu,?_⟩
  have hm : ((ps.length+1:Nat):Int)-1=(ps.length:Int) := by omega
  have hr := target_edge_ready a c ps (run (signedTransport tau) (a::ps))
    (ps.length+1) H (H+tau) tau targetW 0 z u (signedTransport tau)
    (fun d => if d=a then tau else 0) (2*tau.natAbs) (by omega) h hu
    (by simp [hca]) (by ring) (by rw [hm]; exact htarget)
  simpa only [hm] using hr

#print axioms paid_signed
#print axioms signed_target_ready
#print axioms buffer_logical_winding
#print axioms target_edge_ready
#print axioms paid_target_handoff
end LRX.UpperNativeLift
