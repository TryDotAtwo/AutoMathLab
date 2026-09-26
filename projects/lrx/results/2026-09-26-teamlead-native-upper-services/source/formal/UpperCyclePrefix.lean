import UpperSingletonService

/-! Inductive infrastructure for actual cycle prefixes, not cycle existence. -/
namespace LRX.UpperNativeLift
open LRX.BlockExchange LRX.UpperAffineBuffer
variable {α : Type*} [DecidableEq α]

private theorem left_perm' (xs : List α) : xs.Perm (left xs) := by
  cases xs with
  | nil => exact List.Perm.refl _
  | cons a ps => simpa [left] using (List.perm_append_comm : ([a]++ps).Perm (ps++[a]))

theorem native_step_perm (op : Op) (xs : List α) : xs.Perm (step op xs) := by
  cases op with
  | L => exact left_perm' xs
  | R => exact (List.reverse_perm xs).symm.trans ((left_perm' xs.reverse).trans (List.reverse_perm (left xs.reverse)).symm)
  | X =>
    cases xs with
    | nil => exact List.Perm.refl _
    | cons a ps =>
      cases ps with
      | nil => exact List.Perm.refl _
      | cons b qs => exact List.Perm.swap _ _ _

/-- Every native word preserves the whole multiset, not just list length. -/
theorem native_run_perm (word : List Op) (xs : List α) : xs.Perm (run word xs) := by
  induction word generalizing xs with
  | nil => exact List.Perm.refl _
  | cons op ops ih => exact (native_step_perm op xs).trans (ih (step op xs))

theorem PaidEffect.perm {n : Nat} {xs ys : List α} {H K : Int}
    {z u : α → Int} {word : List Op} {delta : α → Int} {cost : Nat}
    (h : PaidEffect n xs ys H K z u word delta cost) : xs.Perm ys := by
  rw [← h.endpoint]
  exact native_run_perm word xs

/-- Extend a certified real prefix by a newly constructed target edge.
The next edge's endpoint and cost are conclusions; its existence is NOT an input.
Previous effects are explicitly subtracted in the original-frame congruence. -/
theorem PaidEffect.extend_target {xs : List α} {a : α} {ps : List α}
    {H K : Int} {z u : α → Int} {word : List Op} {delta : α → Int} {cost : Nat}
    (h : PaidEffect (ps.length+1) xs (a::ps) H K z u word delta cost)
    (hall : ∀ c, c∈xs) (hn : xs.Nodup) (hne : 1≤ps.length)
    (c : α) (tau targetW : Int) (hca : c≠a)
    (ht : contract (ps.length:Int) H (z c)+delta c =
      contract (ps.length:Int) H (z a)+delta a+tau+(ps.length:Int)*targetW) :
    ∃ qs v, ps.length=qs.length+1 ∧
      PaidEffect (ps.length+1) xs (c::a::qs) H (K+tau) z v
        (word++(signedTransport tau++[.X]))
        (fun d => delta d+(if d=a then tau else 0)) (cost+(2*tau.natAbs+1)) := by
  have hm : ((ps.length+1:Nat):Int)-1=(ps.length:Int) := by omega
  have hl (d : α) := h.logical d
  simp only [hm] at hl
  have ht' : contract (ps.length:Int) K (u c)=
      contract (ps.length:Int) K (u a)+tau+(ps.length:Int)*targetW := by
    rw [hl c,hl a]
    exact ht
  obtain ⟨qs,v,hlen,hs⟩ := signed_target_step tau a c ps K targetW u hne
    (fun d => h.perm.mem_iff.mp (hall d)) (h.perm.nodup_iff.mp hn)
    h.represented hca ht'
  exact ⟨qs,v,hlen,h.append hs⟩

/-- At a fresh pair of distinct labels, the original target congruence suffices. -/
theorem PaidEffect.extend_fresh_target {xs : List α} {a : α} {ps : List α}
    {H K : Int} {z u : α → Int} {word : List Op} {delta : α → Int} {cost : Nat}
    (h : PaidEffect (ps.length+1) xs (a::ps) H K z u word delta cost)
    (hall : ∀ c, c∈xs) (hn : xs.Nodup) (hne : 1≤ps.length)
    (c : α) (tau targetW : Int) (hca : c≠a) (ha : delta a=0) (hc : delta c=0)
    (ht : contract (ps.length:Int) H (z c)=
      contract (ps.length:Int) H (z a)+tau+(ps.length:Int)*targetW) :
    ∃ qs v, ps.length=qs.length+1 ∧
      PaidEffect (ps.length+1) xs (c::a::qs) H (K+tau) z v
        (word++(signedTransport tau++[.X]))
        (fun d => delta d+(if d=a then tau else 0)) (cost+(2*tau.natAbs+1)) := by
  apply h.extend_target hall hn hne c tau targetW hca
  simpa only [ha,hc,add_zero] using ht

/-- Construct the last transport and handoff to the untouched parent.
The total head shift is a multiple of M; no return-service premise is used. -/
theorem PaidEffect.close_parent {xs : List α} {a : α} {ps : List α}
    {H K : Int} {z u : α → Int} {word : List Op} {delta : α → Int} {cost : Nat}
    (h : PaidEffect (ps.length+1) xs (a::ps) H K z u word delta cost)
    (hall : ∀ c, c∈xs) (hn : xs.Nodup) (hne : 1≤ps.length)
    (p : α) (tau w wp : Int) (hpa : p≠a) (hp : delta p=0)
    (hparent : contract (ps.length:Int) H (z p)=H+(ps.length:Int)*wp)
    (hframe : K+tau=H+(ps.length:Int)*w) :
    ∃ qs v, ps.length=qs.length+1 ∧
      PaidEffect (ps.length+1) xs (p::a::qs) H (H+(ps.length:Int)*w) z v
        (word++(signedTransport tau++[.X]))
        (fun d => delta d+(if d=a then tau else 0)) (cost+(2*tau.natAbs+1)) := by
  have hm : ((ps.length+1:Nat):Int)-1=(ps.length:Int) := by omega
  obtain ⟨wa,hwa⟩ := buffer_logical_winding a ps (ps.length+1) K u
    (by omega) h.represented
  rw [hm] at hwa
  have hlp := h.logical p
  rw [hm,hp,add_zero,hparent] at hlp
  have ht : contract (ps.length:Int) K (u p)=
      contract (ps.length:Int) K (u a)+tau+(ps.length:Int)*(wp-wa-w) := by
    rw [hlp,hwa]
    calc
      H+(ps.length:Int)*wp = (H+(ps.length:Int)*w)+(ps.length:Int)*wa+
        (ps.length:Int)*(wp-wa-w) := by ring
      _ = K+(ps.length:Int)*wa+tau+(ps.length:Int)*(wp-wa-w) := by rw [← hframe]; ring
  obtain ⟨qs,v,hlen,hs⟩ := signed_target_step tau a p ps K (wp-wa-w) u hne
    (fun d => h.perm.mem_iff.mp (hall d)) (h.perm.nodup_iff.mp hn)
    h.represented hpa ht
  refine ⟨qs,v,hlen,?_⟩
  simpa only [hframe] using h.append hs

#print axioms PaidEffect.close_parent

#print axioms native_step_perm
#print axioms native_run_perm
#print axioms PaidEffect.perm
#print axioms PaidEffect.extend_target
#print axioms PaidEffect.extend_fresh_target
end LRX.UpperNativeLift
