import LRX.UpperScalarPruning
import LRX.UpperScalarRanges

/-! Finite scalar enumeration using the accelerated m/v/x bounds.
The predicate is applied after enumeration; moving its independent conjuncts earlier
is an implementation optimization, not an extra mathematical assumption. -/
namespace LRX.UpperScalarRows

set_option maxRecDepth 2048

def prunedCandidates (k : Int) : Finset Row :=
  (Finset.Icc (2:Int) 12).biUnion fun t =>
  (Finset.Icc (0:Int) 1).biUnion fun p =>
  (Finset.Icc (0:Int) (t+5)).biUnion fun f =>
  (Finset.Icc (0:Int) (3*t+6)).biUnion fun eps =>
  (Finset.Icc (0:Int) f).biUnion fun a =>
  (Finset.Icc (1:Int) (3*t+1)).biUnion fun U =>
  let r0 : Row := ⟨t,p,f,eps,a,U,0,0,0⟩
  (Finset.Icc r0.mLower 1379).biUnion fun m =>
  let r1 : Row := ⟨t,p,f,eps,a,U,m,0,0⟩
  (Finset.Icc r1.vLower (r1.vUpper k)).biUnion fun v =>
  let r2 : Row := ⟨t,p,f,eps,a,U,m,v,0⟩
  ((Finset.Icc (r2.xLower k false) (r2.xUpper k false)) ∪
    (Finset.Icc (r2.xLower k true) (r2.xUpper k true))).image
      fun x => ⟨t,p,f,eps,a,U,m,v,x⟩

theorem admissible_mem_prunedCandidates (k : Int) (r : Row) (h : Admissible k r) :
    r ∈ prunedCandidates k := by
  have hmvr := admissible_mv_covered k r h
  have hxr := admissible_x_covered k r h
  rcases h.2.1 with ⟨ht,ht',hp,hp',hf,hf',he,he',ha,ha',hu,hu',_⟩
  unfold prunedCandidates
  apply Finset.mem_biUnion.mpr
  refine ⟨r.t, Finset.mem_Icc.mpr ⟨ht,ht'⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨r.p, Finset.mem_Icc.mpr ⟨hp,hp'⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨r.f, Finset.mem_Icc.mpr ⟨hf,hf'⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨r.eps, Finset.mem_Icc.mpr ⟨he,he'⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨r.a, Finset.mem_Icc.mpr ⟨ha,ha'⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨r.U, Finset.mem_Icc.mpr ⟨hu,hu'⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨r.m, Finset.mem_Icc.mpr ⟨hmvr.1,hmvr.2.1⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨r.v, Finset.mem_Icc.mpr ⟨hmvr.2.2.1,hmvr.2.2.2⟩, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨r.x, ?_, ?_⟩
  · apply Finset.mem_union.mpr
    rcases hxr with hxr | hxr
    · exact Or.inl (Finset.mem_Icc.mpr hxr)
    · exact Or.inr (Finset.mem_Icc.mpr hxr)
  · cases r
    rfl

def prunedRows (k : Int) : Finset Row := (prunedCandidates k).filter (Admissible k)

theorem mem_prunedRows (k : Int) (r : Row) : r ∈ prunedRows k ↔ Admissible k r := by
  rw [prunedRows, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨admissible_mem_prunedCandidates k r h,h⟩⟩

theorem prunedRows_eq_rows (k : Int) : prunedRows k = rows k := by
  ext r
  rw [mem_prunedRows, mem_rows]

#print axioms admissible_mem_prunedCandidates
#print axioms mem_prunedRows
#print axioms prunedRows_eq_rows
end LRX.UpperScalarRows
