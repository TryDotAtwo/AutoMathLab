import LRX.BlockExchange
import Mathlib.GroupTheory.Perm.Basic

namespace LRX.ReducedPrice
open BlockExchange
variable {α : Type*}

theorem right_left (s : List α) : right (left s) = s := by
  cases s with
  | nil => rfl
  | cons x xs => exact right_append xs x

theorem left_right (s : List α) : left (right s) = s := by
  have h := right_left s.reverse
  simpa [right] using congrArg List.reverse h

def rotation : Equiv.Perm (List α) where
  toFun := left
  invFun := right
  left_inv := right_left
  right_inv := left_right

def spin : Int → List Op
  | .ofNat n => List.replicate n .L
  | .negSucc n => List.replicate (n+1) .R

theorem spin_length (k : Int) : (spin k).length = k.natAbs := by
  cases k <;> simp [spin]

theorem run_replicate (op : Op) (n : Nat) (s : List α) :
    run (List.replicate n op) s = (step op)^[n] s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, run, Function.iterate_succ_apply] using ih (step op s)

theorem run_spin (k : Int) (s : List α) : run (spin k) s = (rotation ^ k) s := by
  cases k with
  | ofNat n => simp [spin, run_replicate, zpow_natCast, Equiv.Perm.coe_pow, rotation]; rfl
  | negSucc n =>
    simp [spin, run_replicate, zpow_negSucc, ← inv_pow, Equiv.Perm.coe_pow, rotation, step]; rfl

theorem spin_add (a b : Int) (s : List α) :
    run (spin (a+b)) s = run (spin b) (run (spin a) s) := by
  simp only [run_spin]
  rw [add_comm a b, zpow_add, Equiv.Perm.coe_mul]
  rfl

/- An affine form keeps signed coefficients explicitly, including multiplicities.
   A term (a,j) denotes a * z_j; repeated indices are summed. -/
structure Affine where
  constant : Int
  terms : List (Int × Nat)

def Affine.eval (f : Affine) (z : Nat → Nat) : Int :=
  f.constant + (f.terms.map fun (a,j) => a * (z j : Int)).sum

def Affine.add (f g : Affine) : Affine :=
  ⟨f.constant + g.constant, f.terms ++ g.terms⟩
def Affine.zero : Affine := ⟨0, []⟩
def Affine.one : Affine := ⟨1, []⟩
def Affine.negOne : Affine := ⟨-1, []⟩
def Affine.coord (j : Nat) (a : Int) (c : Int := 0) : Affine := ⟨c, [(a,j)]⟩

theorem Affine.eval_add (f g : Affine) (z : Nat → Nat) :
    (f.add g).eval z = f.eval z + g.eval z := by
  simp [Affine.add, Affine.eval, List.sum_append]; omega

inductive Core where
  | single
  | leftBlock (j : Nat)
  | rightBlock (j : Nat)

def Core.word (z : Nat → Nat) : Core → List Op
  | .single => [.X]
  | .leftBlock j => [.X] ++ rx (z j)
  | .rightBlock j => [.X] ++ lx (z j)

def Core.extra (z : Nat → Nat) : Core → Nat
  | .single => 0
  | .leftBlock j | .rightBlock j => z j

theorem Core.length_word (z : Nat → Nat) (c : Core) :
    (c.word z).length = 1 + 2 * c.extra z := by
  cases c <;> simp [Core.word, Core.extra, rx_length, lx_length, Nat.add_comm]

inductive Token where
  | rot (f : Affine)
  | core (c : Core)

def Token.word (z : Nat → Nat) : Token → List Op
  | .rot f => spin (f.eval z)
  | .core c => c.word z

def tokensWord (z : Nat → Nat) (ts : List Token) : List Op :=
  ts.flatMap (Token.word z)

/- Accumulate each external rotation gap symbolically; X-delimited cores
   retain their paid internal unit rotations. No XX reduction is performed. -/
def normalize (z : Nat → Nat) (pending : Affine) : List Token → List Op
  | [] => spin (pending.eval z)
  | .rot f :: ts => normalize z (pending.add f) ts
  | .core c :: ts => spin (pending.eval z) ++ c.word z ++ normalize z Affine.zero ts

def gaps (pending : Affine) : List Token → List Affine
  | [] => [pending]
  | .rot f :: ts => gaps (pending.add f) ts
  | .core _ :: ts => pending :: gaps Affine.zero ts

def cores : List Token → List Core
  | [] => []
  | .rot _ :: ts => cores ts
  | .core c :: ts => c :: cores ts

theorem normalize_semantics (z : Nat → Nat) (ts : List Token)
    (p : Affine) (s : List α) :
    run (normalize z p ts) s = run (tokensWord z ts) (run (spin (p.eval z)) s) := by
  induction ts generalizing p s with
  | nil => simp [normalize, tokensWord, run]
  | cons t ts ih =>
    cases t with
    | rot f =>
      simp only [normalize, ih, Affine.eval_add, spin_add, tokensWord,
        List.flatMap_cons, Token.word, run_append]
    | core c =>
      simp [normalize, run_append, ih, Affine.zero, Affine.eval, spin,
        run, tokensWord, Token.word]

theorem normalize_length (z : Nat → Nat) (ts : List Token) (p : Affine) :
    (normalize z p ts).length = (cores ts).length +
      2 * ((cores ts).map (Core.extra z)).sum +
      ((gaps p ts).map fun f => (f.eval z).natAbs).sum := by
  induction ts generalizing p with
  | nil => simp [normalize, cores, gaps, spin_length]
  | cons t ts ih =>
    cases t with
    | rot f => simpa [normalize, cores, gaps] using ih (p.add f)
    | core c =>
      simp only [normalize, List.length_append, spin_length, Core.length_word,
        ih, cores, gaps, List.length_cons, List.map_cons, List.sum_cons]
      omega



/- Symbolic translation of the original state-dependent macros. -/
def macroTokens : Op → List (Atom α) → List Token
  | .L, .named _ :: _ => [.rot Affine.one]
  | .L, .block j :: _ => [.rot (Affine.coord j 1 1)]
  | .R, atoms => match atoms.reverse with
    | .named _ :: _ => [.rot Affine.negOne]
    | .block j :: _ => [.rot (Affine.coord j (-1) (-1))]
    | [] => []
  | .X, .named _ :: .named _ :: _ => [.core .single]
  | .X, .block j :: .named _ :: _ =>
      [.rot (Affine.coord j 1), .core (.leftBlock j)]
  | .X, .named _ :: .block j :: _ =>
      [.core (.rightBlock j), .rot (Affine.coord j (-1))]
  | _, _ => []

theorem spin_nat (n : Nat) : spin (n : Int) = List.replicate n .L := rfl

theorem spin_neg_nat (n : Nat) : spin (-(n : Int)) = List.replicate n .R := by
  cases n with
  | zero => rfl
  | succ n => rfl

theorem macroTokens_word (z : Nat → Nat) (op : Op) (atoms : List (Atom α)) :
    tokensWord z (macroTokens op atoms) = macroFor z op atoms := by
  cases op with
  | L =>
    cases atoms with
    | nil => rfl
    | cons a atoms =>
      cases a with
      | named x => rfl
      | block j =>
        have hc : (1 : Int) + (z j : Int) = ((z j + 1 : Nat) : Int) := by omega
        simp only [macroTokens, tokensWord, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, Token.word, Affine.coord, Affine.eval, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero, hc]
        rfl
  | R =>
    cases h : atoms.reverse with
    | nil => simp [macroTokens, macroFor, h, tokensWord]
    | cons a atoms' =>
      cases a with
      | named x => simp [macroTokens, macroFor, h, tokensWord, Token.word,
          Affine.negOne, Affine.eval, spin]; rfl
      | block j =>
        have hn : (-1 : Int) + -(z j : Int) = -((z j + 1 : Nat) : Int) := by omega
        simp only [macroTokens, macroFor, h, tokensWord, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, Token.word, Affine.coord, Affine.eval,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, neg_one_mul,
          add_zero, hn, spin_neg_nat]
  | X =>
    cases atoms with
    | nil => rfl
    | cons a atoms =>
      cases atoms with
      | nil => cases a <;> rfl
      | cons b atoms => cases a <;> cases b <;>
          simp [macroTokens, macroFor, tokensWord, Token.word, Core.word,
            Affine.coord, Affine.eval, leftMacro, rightMacro, spin_nat,
            spin_neg_nat, List.append_assoc]

def compile : List Op → List (Atom α) → List Token
  | [], _ => []
  | op :: ops, atoms => macroTokens op atoms ++ compile ops (step op atoms)

theorem compile_word (z : Nat → Nat) (ops : List Op) (atoms : List (Atom α)) :
    tokensWord z (compile ops atoms) = liftWord z ops atoms := by
  induction ops generalizing atoms with
  | nil => rfl
  | cons op ops ih =>
    simp only [compile, tokensWord, List.flatMap_append]
    change tokensWord z (macroTokens op atoms) ++ tokensWord z (compile ops (step op atoms)) = _
    rw [macroTokens_word, ih]
    rfl

def reducedLift (z : Nat → Nat) (ops : List Op) (atoms : List (Atom α)) : List Op :=
  normalize z Affine.zero (compile ops atoms)

theorem reducedLift_endpoint (zero : α) (z : Nat → Nat)
    (ops : List Op) (atoms : List (Atom α)) :
    run (reducedLift z ops atoms) (expand zero z atoms) = expand zero z (run ops atoms) := by
  rw [reducedLift, normalize_semantics, compile_word]
  simpa [Affine.zero, Affine.eval, spin, run] using run_liftWord zero z ops atoms

/- Admissibility excludes X00 and vacuous X on fewer than two atoms.
   All source sorting words on at least two atoms without X00 satisfy it. -/
def ValidStep : Op → List (Atom α) → Prop
  | .X, .named _ :: .named _ :: _ => True
  | .X, .named _ :: .block _ :: _ => True
  | .X, .block _ :: .named _ :: _ => True
  | .X, _ => False
  | _, _ => True

def ValidWord : List Op → List (Atom α) → Prop
  | [], _ => True
  | op :: ops, atoms => ValidStep op atoms ∧ ValidWord ops (step op atoms)

def xCount : List Op → Nat
  | [] => 0
  | .X :: ops => 1 + xCount ops
  | _ :: ops => xCount ops

def swapBlocks : List Op → List (Atom α) → List Nat
  | [], _ => []
  | op :: ops, atoms =>
    (match op, atoms with
      | .X, .block j :: .named _ :: _ => [j]
      | .X, .named _ :: .block j :: _ => [j]
      | _, _ => []) ++ swapBlocks ops (step op atoms)

def Core.blockIndex : Core → Option Nat
  | .single => none
  | .leftBlock j | .rightBlock j => some j

theorem cores_append (u v : List Token) : cores (u ++ v) = cores u ++ cores v := by
  induction u with
  | nil => rfl
  | cons t u ih => cases t <;> simp [cores, ih]

theorem compile_core_count (ops : List Op) (atoms : List (Atom α))
    (h : ValidWord ops atoms) : (cores (compile ops atoms)).length = xCount ops := by
  induction ops generalizing atoms with
  | nil => rfl
  | cons op ops ih =>
    rw [compile, cores_append, List.length_append, ih _ h.2]
    cases op with
    | L => cases atoms with
      | nil => simp [macroTokens, cores, xCount]
      | cons a atoms => cases a <;> simp [macroTokens, cores, xCount]
    | R => cases hr : atoms.reverse with
      | nil => simp [macroTokens, hr, cores, xCount]
      | cons a atoms' => cases a <;> simp [macroTokens, hr, cores, xCount]
    | X =>
      have hv := h.1
      cases atoms with
      | nil => exact False.elim hv
      | cons a atoms =>
        cases atoms with
        | nil => cases a <;> exact False.elim hv
        | cons b atoms => cases a <;> cases b <;>
            simp_all [ValidStep, macroTokens, cores, xCount]

theorem compile_blocks (ops : List Op) (atoms : List (Atom α)) :
    (cores (compile ops atoms)).filterMap Core.blockIndex = swapBlocks ops atoms := by
  induction ops generalizing atoms with
  | nil => rfl
  | cons op ops ih =>
    rw [compile, cores_append, List.filterMap_append, ih]
    cases op with
    | L => cases atoms with
      | nil => rfl
      | cons a atoms => cases a <;> rfl
    | R => cases hr : atoms.reverse with
      | nil => simp [macroTokens, hr, cores, swapBlocks]
      | cons a atoms' => cases a <;> simp [macroTokens, hr, cores, swapBlocks]
    | X => cases atoms with
      | nil => rfl
      | cons a atoms => cases atoms with
        | nil => cases a <;> rfl
        | cons b atoms => cases a <;> cases b <;> rfl

theorem core_extras (z : Nat → Nat) (cs : List Core) :
    (cs.map (Core.extra z)).sum = ((cs.filterMap Core.blockIndex).map z).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [Core.extra, Core.blockIndex, List.filterMap, ih]

/-- Exact paid length; block indices occur once per base exchange with that block.
    Thus the middle sum is Σ_j s_j z_j with multiplicities s_j. -/
theorem reducedLift_length (z : Nat → Nat) (ops : List Op) (atoms : List (Atom α))
    (h : ValidWord ops atoms) :
    (reducedLift z ops atoms).length = xCount ops +
      2 * ((swapBlocks ops atoms).map z).sum +
      ((gaps Affine.zero (compile ops atoms)).map fun f => (f.eval z).natAbs).sum := by
  rw [reducedLift, normalize_length, compile_core_count _ _ h, core_extras, compile_blocks]

/-- The source claim combines actual endpoint semantics and the exact cost. -/
theorem reducedLift_correct (zero : α) (z : Nat → Nat)
    (ops : List Op) (atoms target : List (Atom α))
    (h : ValidWord ops atoms) (ht : run ops atoms = target) :
    run (reducedLift z ops atoms) (expand zero z atoms) = expand zero z target ∧
    (reducedLift z ops atoms).length = xCount ops +
      2 * ((swapBlocks ops atoms).map z).sum +
      ((gaps Affine.zero (compile ops atoms)).map fun f => (f.eval z).natAbs).sum := by
  exact ⟨(reducedLift_endpoint zero z ops atoms).trans (congrArg (expand zero z) ht),
    reducedLift_length z ops atoms h⟩

theorem normalize_length_le (z : Nat → Nat) (ts : List Token) (p : Affine) :
    (normalize z p ts).length ≤ (p.eval z).natAbs + (tokensWord z ts).length := by
  induction ts generalizing p with
  | nil => simp [normalize, tokensWord, spin_length]
  | cons t ts ih =>
    cases t with
    | rot f =>
      have h := ih (p.add f)
      have ha := Int.natAbs_add_le (p.eval z) (f.eval z)
      simp only [Affine.eval_add] at h
      simp only [normalize, tokensWord, List.flatMap_cons, Token.word,
        List.length_append, spin_length]
      change (normalize z (p.add f) ts).length ≤ _
      dsimp [tokensWord, Affine.zero] at *
      omega
    | core c =>
      have h := ih Affine.zero
      simp only [Affine.zero, Affine.eval, List.map_nil, List.sum_nil,
        add_zero, Int.natAbs_zero, zero_add] at h
      simp only [normalize, List.length_append, spin_length, tokensWord,
        List.flatMap_cons, Token.word]
      dsimp [tokensWord, Affine.zero] at *
      omega

theorem reducedLift_length_le_raw (z : Nat → Nat) (ops : List Op)
    (atoms : List (Atom α)) :
    (reducedLift z ops atoms).length ≤ (liftWord z ops atoms).length := by
  have h := normalize_length_le z (compile ops atoms) Affine.zero
  simpa [reducedLift, compile_word, Affine.zero, Affine.eval] using h

#print axioms reducedLift_correct
#print axioms reducedLift_length_le_raw
end LRX.ReducedPrice
