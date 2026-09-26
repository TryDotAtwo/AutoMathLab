import UpperNativeLift

/-! Full native-label coverage and exact paid macro preservation.
Local bridge only: no recursive service or universal cost bound. -/
namespace LRX.UpperNativeLift
open LRX.BlockExchange
open LRX.UpperAffineBuffer
variable {α : Type*}

private theorem negmod (u n : Int) : (- (u % n)) % n = (-u) % n := by
  have h := Int.sub_emod 0 u n
  simpa using h.symm

/-- Full label coverage turns a native lift into a complete affine state. -/
theorem residue_complete (xs : List α) (H : Int) (z : α → Int)
    (hall : ∀ a, a ∈ xs) (h : Represents xs.length H xs z) :
    ResidueComplete ((xs.length:Int)-1) H z := by
  have hn : (xs.length:Int)-1+1=(xs.length:Int) := by omega
  have flip (a : α) : (-(H-z a)) = z a-H := by ring
  constructor
  · intro a b he
    obtain ⟨i,hi,hai⟩ := List.mem_iff_getElem.mp (hall a)
    obtain ⟨j,hj,hbj⟩ := List.mem_iff_getElem.mp (hall b)
    have hip := native_residue xs H z h i hi
    have hjp := native_residue xs H z h j hj
    rw [hai] at hip
    rw [hbj] at hjp
    have hh := congrArg (fun r : Int => (-r) % (xs.length:Int)) he
    simp only [hn, negmod, flip, hip, hjp] at hh
    have hij : i=j := by exact_mod_cast hh
    subst j
    exact hai.symm.trans hbj
  · intro r hr hlt
    rw [hn] at hlt ⊢
    let i : Nat := if r=0 then 0 else (xs.length:Int).toNat-r.toNat
    have hi : i<xs.length := by dsimp [i]; split_ifs <;> omega
    refine ⟨xs[i], ?_⟩
    have hp := native_residue xs H z h i hi
    have hh := congrArg (fun v : Int => (-v) % (xs.length:Int)) hp
    rw [negmod] at hh
    have hh' : (H-z xs[i])%(xs.length:Int)=(-(i:Int))%(xs.length:Int) := by
      convert hh using 1; ring_nf
    rw [hh']
    by_cases hz : r=0
    · simp [i,hz]
    · have he : (i:Int)=(xs.length:Int)-r := by dsimp [i]; simp only [hz,ite_false]; omega
      rw [he]
      have he' : -((xs.length:Int)-r)=r-(xs.length:Int) := by ring
      rw [he',Int.sub_emod,Int.emod_self,sub_zero,Int.emod_emod,Int.emod_eq_of_lt hr hlt]

/-- Native completeness gives the unique canonical affine buffer. -/
theorem native_unique_buffer (xs : List α) (H : Int) (z : α → Int)
    (hall : ∀ a, a ∈ xs) (hlen : 2 ≤ xs.length)
    (h : Represents xs.length H xs z) :
    ∃! a, decide ((H-z a) % (xs.length:Int)=0)=true := by
  have hc := residue_complete xs H z hall h
  have hM : (0:Int)<(xs.length:Int)-1 := by omega
  have hd := state_decode ((xs.length:Int)-1) H z hM
  have hu := state_exactly_one_buffer ((xs.length:Int)-1) H _ _ z hM hc hd
  simpa using hu

/-- Paid XL keeps the distinguished label at the head in the new frame. -/
theorem macro_XL [DecidableEq α] (a b : α) (ps : List α) (H : Int) (z : α → Int)
    (hn : (a::b::ps).Nodup)
    (h : Represents (ps.length+2) H (a::b::ps) z) :
    Represents (ps.length+2) (H+1) (run [.X,.L] (a::b::ps)) (exchange a b z) := by
  have hx := step_X a b ps H z hn h
  have hl := step_L b (a::ps) H (exchange a b z) hx
  simpa [run,step,swap] using hl

/-- Paid RX has the dual winding-aware native lift. -/
theorem macro_RX [DecidableEq α] (a b : α) (ps : List α) (H : Int) (z : α → Int)
    (hn : ((a::ps)++[b]).Nodup)
    (h : Represents (ps.length+2) H ((a::ps)++[b]) z) :
    Represents (ps.length+2) (H-1) (run [.R,.X] ((a::ps)++[b])) (exchange b a z) := by
  have hr := step_R (a::ps) b H z h
  have hn' : (b::a::ps).Nodup := by
    have hperm : ((a::ps)++[b]).Perm (b::a::ps) := List.perm_append_comm
    exact hperm.nodup_iff.mp hn
  change Represents (ps.length+2) (H-1) (right ((a::ps)++[b])) z at hr
  rw [right_append] at hr
  have hx := step_X b a ps (H-1) z hn' hr
  change Represents (ps.length+2) (H-1) (swap (right ((a::ps)++[b]))) (exchange b a z)
  rw [right_append]
  exact hx

/-- Canonical decoding represents every label, and its buffer is precisely the
first native label (not an independently postulated distinguished label). -/
theorem decoded_head (a : α) (ps : List α) (H : Int) (z : α → Int)
    (hall : ∀ c, c ∈ a::ps) (hlen : 1 ≤ ps.length)
    (h : Represents (ps.length+1) H (a::ps) z) :
    StateRepresents (ps.length:Int) H
      (fun c => decide ((H-z c)%((ps.length:Int)+1)=0))
      (fun c => contract (ps.length:Int) H (z c)) z ∧
    ∀ c, decide ((H-z c)%((ps.length:Int)+1)=0)=true ↔ c=a := by
  have hM : (0:Int)<ps.length := by omega
  refine ⟨state_decode (ps.length:Int) H z hM, ?_⟩
  have hc := residue_complete (a::ps) H z hall h
  have hp := native_residue (a::ps) H z h 0 (by simp)
  simp only [List.getElem_cons_zero, List.length_cons, Nat.cast_add, Nat.cast_one, Nat.cast_zero] at hp
  have ha : (H-z a)%((ps.length:Int)+1)=0 := by
    have hh := congrArg (fun v : Int => (-v)%((ps.length:Int)+1)) hp
    rw [negmod] at hh
    have he : -(z a-H)=H-z a := by ring
    simpa [he] using hh
  intro c
  simp only [decide_eq_true_eq]
  constructor
  · intro hh
    apply hc.1
    simpa using hh.trans ha.symm
  · intro hh
    simpa [hh] using ha

#print axioms residue_complete
#print axioms native_unique_buffer
#print axioms macro_XL
#print axioms macro_RX
#print axioms decoded_head
end LRX.UpperNativeLift
