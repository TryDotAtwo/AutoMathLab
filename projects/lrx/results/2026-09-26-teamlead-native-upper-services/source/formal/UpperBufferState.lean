import UpperBufferRepresents

/-! Labelled affine states for U19 §4. Physical coordinates cover all residues
exactly once; arbitrary integer windings are retained. This does NOT yet
identify native list operations with affine state transitions. -/
namespace LRX.UpperAffineBuffer

variable {α : Type*}

def ResidueComplete (M H : Int) (z : α → Int) : Prop :=
  (Function.Injective fun a => (H-z a)%(M+1)) ∧
  ∀ r : Int, 0 ≤ r → r < M+1 → ∃ a, (H-z a)%(M+1)=r

def StateRepresents (M H : Int) (b : α → Bool) (y z : α → Int) : Prop :=
  ∀ a, Represents M H (b a) (y a) (z a)

/-- A residue-complete labelled physical state always admits canonical decoding. -/
theorem state_decode (M H : Int) (z : α → Int) (hM : 0<M) :
    StateRepresents M H (fun a => decide ((H-z a)%(M+1)=0))
      (fun a => contract M H (z a)) z := by
  intro a
  exact represents_decode M H (z a) hM

/-- The decoded state is unique, including all integer windings. -/
theorem state_unique (M H : Int) (b b' : α → Bool) (y y' z : α → Int)
    (hM : 0<M) (h : StateRepresents M H b y z)
    (h' : StateRepresents M H b' y' z) : b=b' ∧ y=y' := by
  constructor
  · funext a
    exact (represents_unique M H (y a) (y' a) (z a) (b a) (b' a) hM (h a) (h' a)).1
  · funext a
    exact (represents_unique M H (y a) (y' a) (z a) (b a) (b' a) hM (h a) (h' a)).2

/-- Completeness, not a choice of a distinguished label, supplies the buffer. -/
theorem state_exactly_one_buffer (M H : Int) (b : α → Bool) (y z : α → Int)
    (hM : 0<M) (hc : ResidueComplete M H z)
    (h : StateRepresents M H b y z) : ∃! a, b a=true := by
  obtain ⟨a,ha⟩ := hc.2 0 (by omega) (by omega)
  refine ⟨a, (represents_tag M H (y a) (z a) (b a) hM (h a)).2 ha, ?_⟩
  intro a' hb
  apply hc.1
  have hz := (represents_tag M H (y a') (z a') (b a') hM (h a')).1 hb
  exact hz.trans ha.symm

/-- Distinct labels cannot collide as tagged integer logical coordinates. -/
theorem state_tagged_injective (M H : Int) (b : α → Bool) (y z : α → Int)
    (hc : ResidueComplete M H z) (h : StateRepresents M H b y z) :
    Function.Injective (fun a => (b a, y a)) := by
  intro a a' he
  have hb : b a = b a' := congrArg Prod.fst he
  have hy : y a = y a' := congrArg Prod.snd he
  have hz : z a = z a' := by
    calc
      z a = (if b a then buffer M H (y a) else passive M H (y a)) := (h a).1
      _ = (if b a' then buffer M H (y a') else passive M H (y a')) := by rw [hb,hy]
      _ = z a' := (h a').1.symm
  apply hc.1
  change (H-z a)%(M+1) = (H-z a')%(M+1)
  rw [hz]

/-- A full labelled state can be re-decoded at another head. This is a frame
change, NOT an assertion that any physical L/R/X word has been executed. -/
theorem state_reframe (M H d : Int) (z : α → Int) (hM : 0<M) :
    StateRepresents M (H+d) (fun a => decide ((H+d-z a)%(M+1)=0))
      (fun a => contract M (H+d) (z a)) z :=
  state_decode M (H+d) z hM

/-- Physical slot permutation with arbitrary (not necessarily balanced) windings.
The sign convention uses residues H-z; no native list orientation is inferred. -/
def liftedSlots {n : Nat} (H : Int) (p : Equiv.Perm (Fin n))
    (w : Fin n → Int) (a : Fin n) : Int := H-(p a).val+(n:Int)*w a

theorem liftedSlots_residue {n : Nat} (H : Int) (p : Equiv.Perm (Fin n))
    (w : Fin n → Int) (a : Fin n) :
    (H-liftedSlots H p w a)%(n:Int) = (p a).val := by
  have hr : (0:Int) ≤ (p a).val := by omega
  have hn : ((p a).val:Int) < (n:Int) := by exact_mod_cast (p a).isLt
  have hz : H-liftedSlots H p w a = (p a).val-(n:Int)*w a := by
    unfold liftedSlots
    ring
  rw [hz, Int.sub_emod, Int.mul_emod_right, sub_zero, Int.emod_emod,
    Int.emod_eq_of_lt hr hn]

/-- Non-vacuity: every finite slot permutation, with every integer winding
assignment, gives a complete labelled affine state. -/
theorem liftedSlots_complete {n : Nat} (H : Int) (p : Equiv.Perm (Fin n))
    (w : Fin n → Int) : ResidueComplete ((n:Int)-1) H (liftedSlots H p w) := by
  have hn : (n:Int)-1+1=(n:Int) := by omega
  constructor
  · intro a a' he
    simp only [hn, liftedSlots_residue] at he
    apply p.injective
    apply Fin.ext
    exact_mod_cast he
  · intro r hr hlt
    have hrn : r.toNat < n := by omega
    let b : Fin n := ⟨r.toNat,hrn⟩
    refine ⟨p.symm b, ?_⟩
    rw [hn, liftedSlots_residue, p.apply_symm_apply]
    change (r.toNat:Int)=r
    omega

#print axioms liftedSlots_residue
#print axioms liftedSlots_complete
#print axioms state_decode
#print axioms state_unique
#print axioms state_exactly_one_buffer
#print axioms state_tagged_injective
#print axioms state_reframe
end LRX.UpperAffineBuffer
