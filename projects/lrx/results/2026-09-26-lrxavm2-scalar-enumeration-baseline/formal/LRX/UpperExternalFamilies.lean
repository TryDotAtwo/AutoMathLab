import Mathlib.Data.List.Permutation
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Union

/-! A finite catalogue and family enumeration for the external permutations.
The scalar bound mass - 2*(count-1) ≤ 5 remains an explicit hypothesis.
The catalogue does not yet compute the C++ SCC/credit/sign statistics. -/
namespace LRX.UpperExternalFamilies

def Connected (p : List Nat) : Prop :=
  ∀ e ∈ Finset.range (p.length-1), ∃ i ∈ Finset.range p.length,
    (i ≤ e ∧ e < p[i]!) ∨ (p[i]! ≤ e ∧ e < i)

instance (p : List Nat) : Decidable (Connected p) := by
  unfold Connected
  infer_instance

def Valid (p : List Nat) : Prop :=
  p.Perm (List.range p.length) ∧ 2 ≤ p.length ∧ Connected p

def catalogue : Finset (List Nat) :=
  ((Finset.Icc (2:Nat) 5).biUnion fun n =>
    (List.range n).permutations'.toFinset).filter Connected

theorem mem_catalogue (p : List Nat) :
    p ∈ catalogue ↔ Valid p ∧ p.length ≤ 5 := by
  simp only [catalogue, Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_Icc, List.mem_toFinset, List.mem_permutations']
  constructor
  · rintro ⟨⟨n, hn, hp⟩, hc⟩
    have he : p.length = n := by simpa using hp.length_eq
    subst n
    exact ⟨⟨hp,hn.1,hc⟩,hn.2⟩
  · rintro ⟨⟨hp,hl,hc⟩,hu⟩
    exact ⟨⟨p.length,⟨hl,hu⟩,hp⟩,hc⟩

def mass (ps : List (List Nat)) : Nat := (ps.map List.length).sum

theorem mass_lower (ps : List (List Nat)) (h : ∀ p ∈ ps, 2 ≤ p.length) :
    2*ps.length ≤ mass ps := by
  induction ps with
  | nil => simp [mass]
  | cons p ps ih =>
    have hp := h p (by simp)
    have hs := ih (fun q hq => h q (by simp [hq]))
    simp only [mass, List.map_cons, List.sum_cons, List.length_cons] at *
    omega

theorem member_mass_bound (ps : List (List Nat)) (p : List Nat)
    (h : ∀ q ∈ ps, 2 ≤ q.length) (hp : p ∈ ps) :
    p.length + 2*(ps.length-1) ≤ mass ps := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
    have hq := h q (by simp)
    have hqs : ∀ r ∈ qs, 2 ≤ r.length := fun r hr => h r (by simp [hr])
    rcases List.mem_cons.mp hp with he | hm
    · subst p
      have hl := mass_lower qs hqs
      simp only [mass, List.map_cons, List.sum_cons, List.length_cons] at *
      omega
    · have hs := ih hqs hm
      have hn : 1 ≤ qs.length := List.length_pos_of_mem hm
      simp only [mass, List.map_cons, List.sum_cons, List.length_cons] at *
      omega

/-- This uses, and does not establish, the five-point scalar cap. -/
theorem catalogue_coverage (ps : List (List Nat))
    (hv : ∀ p ∈ ps, Valid p) (hcap : mass ps - 2*(ps.length-1) ≤ 5) :
    ∀ p ∈ ps, p ∈ catalogue := by
  intro p hp
  apply (mem_catalogue p).2
  refine ⟨hv p hp, ?_⟩
  have hs := member_mass_bound ps p (fun q hq => (hv q hq).2.1) hp
  omega

def families : Nat → Nat → Finset (List (List Nat))
  | 0, v => if v = 0 then {[]} else ∅
  | t+1, v => catalogue.biUnion fun p =>
      if p.length ≤ v then (families t (v-p.length)).image (p :: ·) else ∅

theorem family_coverage (ps : List (List Nat))
    (h : ∀ p ∈ ps, p ∈ catalogue) : ps ∈ families ps.length (mass ps) := by
  induction ps with
  | nil => simp [families, mass]
  | cons p ps ih =>
    have hp := h p (by simp)
    have hs := ih (fun q hq => h q (by simp [hq]))
    simp only [List.length_cons, mass, List.map_cons, List.sum_cons, families]
    rw [Finset.mem_biUnion]
    refine ⟨p,hp,?_⟩
    rw [if_pos (by omega)]
    simp only [Nat.add_sub_cancel_left]
    exact Finset.mem_image.mpr ⟨ps,hs,rfl⟩

theorem bounded_valid_family_covered (ps : List (List Nat))
    (hv : ∀ p ∈ ps, Valid p) (hcap : mass ps - 2*(ps.length-1) ≤ 5) :
    ps ∈ families ps.length (mass ps) :=
  family_coverage ps (catalogue_coverage ps hv hcap)

theorem family_sound (t v : Nat) (ps : List (List Nat))
    (h : ps ∈ families t v) :
    ps.length = t ∧ mass ps = v ∧ ∀ p ∈ ps, p ∈ catalogue := by
  induction t generalizing v ps with
  | zero =>
    simp only [families] at h
    split_ifs at h with hv
    · simp only [Finset.mem_singleton] at h
      subst ps
      simp [mass, hv]
    · simp at h
  | succ t ih =>
    simp only [families, Finset.mem_biUnion] at h
    obtain ⟨p,hp,h⟩ := h
    split_ifs at h with hv
    · obtain ⟨qs,hqs,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hl,hm,hc⟩ := ih _ _ hqs
      refine ⟨by simp [hl], ?_, ?_⟩
      · simp only [mass, List.map_cons, List.sum_cons] at *
        omega
      · intro q hq
        rcases List.mem_cons.mp hq with he | he
        · simpa [he] using hp
        · exact hc q he
    · simp at h

theorem mem_families (t v : Nat) (ps : List (List Nat)) :
    ps ∈ families t v ↔
      ps.length = t ∧ mass ps = v ∧ ∀ p ∈ ps, p ∈ catalogue := by
  constructor
  · exact family_sound t v ps
  · rintro ⟨rfl,rfl,h⟩
    exact family_coverage ps h

#print axioms mem_catalogue
#print axioms mass_lower
#print axioms member_mass_bound
#print axioms catalogue_coverage
#print axioms family_coverage
#print axioms bounded_valid_family_covered
#print axioms family_sound
#print axioms mem_families
end LRX.UpperExternalFamilies
