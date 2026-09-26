import UpperTargetEdge

/-! Constructive target-edge execution, with endpoint and cost derived.
This is a step toward a closed returning cycle, not its existence theorem. -/
namespace LRX.UpperNativeLift
open LRX.BlockExchange LRX.UpperBufferNative LRX.UpperAffineBuffer
variable {α : Type*} [DecidableEq α]

private theorem left_perm (xs : List α) : xs.Perm (left xs) := by
  cases xs with
  | nil => exact List.Perm.refl _
  | cons a ps => simpa [left] using (List.perm_append_comm : ([a]++ps).Perm (ps++[a]))

private theorem right_perm (xs : List α) : xs.Perm (right xs) := by
  exact (List.reverse_perm xs).symm.trans ((left_perm xs.reverse).trans (List.reverse_perm (left xs.reverse)).symm)

private theorem iterate_perm (f : List α → List α)
    (hf : ∀ xs : List α, xs.Perm (f xs)) (k : Nat) (xs : List α) :
    xs.Perm ((f^[k]) xs) := by
  induction k generalizing xs with
  | zero => exact List.Perm.refl _
  | succ k ih =>
    simpa [Function.iterate_succ_apply] using (hf xs).trans (ih (f xs))

/-- Signed transport preserves the actual head and permutes only its tail. -/
theorem signed_native_shape (tau : Int) (a : α) (ps : List α) :
    ∃ qs, ps.Perm qs ∧ run (signedTransport tau) (a::ps)=a::qs := by
  cases tau with
  | ofNat k => exact ⟨_,iterate_perm left left_perm k ps,run_forward k a ps⟩
  | negSucc k => exact ⟨_,iterate_perm right right_perm (k+1) ps,run_backward (k+1) a ps⟩

/-- No supplied service certificate or endpoint: a target congruence constructs
an actual native word ending with c as buffer. Includes tau=0 and both signs. -/
theorem signed_target_step (tau : Int) (a c : α) (ps : List α)
    (H targetW : Int) (z : α → Int)
    (hne : 1≤ps.length) (hall : ∀ d, d∈a::ps) (hn : (a::ps).Nodup)
    (h : Represents (ps.length+1) H (a::ps) z) (hca : c≠a)
    (htarget : contract (ps.length:Int) H (z c)=
      contract (ps.length:Int) H (z a)+tau+(ps.length:Int)*targetW) :
    ∃ qs u, ps.length=qs.length+1 ∧
      PaidEffect (ps.length+1) (a::ps) (c::a::qs) H (H+tau) z u
        (signedTransport tau++[.X]) (fun d => if d=a then tau else 0)
        (2*tau.natAbs+1) := by
  obtain ⟨ys,hperm,hshape⟩ := signed_native_shape tau a ps
  have hlen := hperm.length_eq
  cases ys with
  | nil =>
    have he : ps.length=0 := hlen
    omega
  | cons b qs =>
    have he : ps.length=qs.length+1 := by simpa using hlen
    obtain ⟨u,hu,hr⟩ := signed_target_ready tau a c ps H targetW z hne hall hn h hca htarget
    rw [hshape] at hu
    have hn' : (a::b::qs).Nodup := (List.Perm.cons a hperm).nodup_iff.mp hn
    have hc : c∈a::b::qs := (List.Perm.cons a hperm).mem_iff.mp (hall c)
    have hu' : Represents (qs.length+2) (H+tau) (a::b::qs) u := by
      simpa only [he,Nat.add_assoc] using hu.represented
    have hr' : (contract ((qs.length:Int)+1) (H+tau) (u c)-(H+tau))%((qs.length:Int)+1)=0 := by
      simpa only [he,Nat.cast_add,Nat.cast_one] using hr
    have hx := paid_ready_handoff a b qs (H+tau) u hn' hu' c hc hca hr'
    have hx' : PaidEffect (ps.length+1) (a::b::qs) (c::a::qs) (H+tau) (H+tau) u
        (exchange a c u) [.X] (fun _ => 0) 1 := by
      simpa only [he,Nat.add_assoc] using hx
    refine ⟨qs,exchange a c u,he,?_⟩
    simpa only [add_zero] using hu.append hx'

#print axioms signed_native_shape
#print axioms signed_target_step
end LRX.UpperNativeLift
