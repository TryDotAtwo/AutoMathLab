import Mathlib.Tactic.Linarith

/-! Concrete L/R/X list semantics and paid macros exchanging a repeated block
with an adjacent atom. Independent namespace; no hypothesis about an optimizer,
affine profiles, or a global diameter theorem. -/
namespace LRX.BlockExchange
variable {α : Type*}

inductive Op where
  | L | R | X

def left : List α → List α
  | [] => []
  | x :: xs => xs ++ [x]
def right (xs : List α) : List α := (left xs.reverse).reverse
def swap : List α → List α
  | x :: y :: xs => y :: x :: xs
  | xs => xs
def step (op : Op) (s : List α) : List α :=
  match op with
  | .L => left s
  | .R => right s
  | .X => swap s
def run : List Op → List α → List α
  | [], s => s
  | op :: ops, s => run ops (step op s)

theorem run_append (u v : List Op) (s : List α) :
    run (u ++ v) s = run v (run u s) := by
  induction u generalizing s with
  | nil => rfl
  | cons op ops ih => simpa [run] using ih (step op s)

theorem right_append (xs : List α) (x : α) : right (xs ++ [x]) = x :: xs := by
  simp [right, left]

theorem replicate_append_one (n : Nat) (z : α) :
    List.replicate n z ++ [z] = List.replicate (n+1) z := by
  induction n with
  | zero => simp
  | succ n ih => simpa [List.replicate_succ] using congrArg (List.cons z) ih

theorem rotate_left_block (n : Nat) (z : α) (xs : List α) :
    run (List.replicate n Op.L) (List.replicate n z ++ xs) = xs ++ List.replicate n z := by
  induction n generalizing xs with
  | zero => simp [run]
  | succ n ih =>
    simpa [List.replicate_succ, run, step, left, List.append_assoc] using ih (xs ++ [z])

theorem rotate_right_block (n : Nat) (z : α) (xs : List α) :
    run (List.replicate n Op.R) (xs ++ List.replicate n z) = List.replicate n z ++ xs := by
  induction n generalizing xs with
  | zero => simp [run]
  | succ n ih =>
    calc
      run (List.replicate (n+1) Op.R) (xs ++ List.replicate (n+1) z)
          = run (List.replicate n Op.R) (z :: (xs ++ List.replicate n z)) := by
            rw [← replicate_append_one n z, ← List.append_assoc]
            simp only [List.replicate_succ, run, step, right_append]
      _ = List.replicate n z ++ (z :: xs) := by
            simpa using ih (z :: xs)
      _ = List.replicate (n+1) z ++ xs := by
            rw [← replicate_append_one n z]
            simp [List.append_assoc]

def rx : Nat → List Op
  | 0 => []
  | n+1 => [Op.R, Op.X] ++ rx n

def lx : Nat → List Op
  | 0 => []
  | n+1 => [Op.L, Op.X] ++ lx n

theorem rx_step (x z : α) (xs : List α) :
    run [Op.R, Op.X] ((x :: xs) ++ [z]) = x :: z :: xs := by
  simp only [run, step, right_append, swap]

theorem rx_transfer (n : Nat) (z x : α) (xs : List α) :
    run (rx n) (x :: (xs ++ List.replicate n z)) =
      x :: (List.replicate n z ++ xs) := by
  induction n generalizing xs with
  | zero => simp [rx, run]
  | succ n ih =>
    calc
      run (rx (n+1)) (x :: (xs ++ List.replicate (n+1) z))
          = run (rx n) (x :: z :: (xs ++ List.replicate n z)) := by
            rw [← replicate_append_one n z, ← List.append_assoc]
            change run ([Op.R, Op.X] ++ rx n) ((x :: (xs ++ List.replicate n z)) ++ [z]) = _
            rw [run_append, rx_step]
      _ = x :: (List.replicate n z ++ (z :: xs)) := by simpa using ih (z :: xs)
      _ = x :: (List.replicate (n+1) z ++ xs) := by
            rw [← replicate_append_one n z]
            simp [List.append_assoc]

theorem lx_transfer (n : Nat) (z x : α) (xs : List α) :
    run (lx n) (z :: x :: (List.replicate n z ++ xs)) =
      z :: x :: (xs ++ List.replicate n z) := by
  induction n generalizing xs with
  | zero => simp [lx, run]
  | succ n ih =>
    simpa [lx, run, step, left, swap, List.replicate_succ, List.append_assoc] using ih (xs ++ [z])

def leftMacro (n : Nat) : List Op := List.replicate n Op.L ++ [Op.X] ++ rx n
def rightMacro (n : Nat) : List Op := [Op.X] ++ lx n ++ List.replicate n Op.R

theorem exchange_left_block (n : Nat) (z x : α) (xs : List α) :
    run (leftMacro n) (List.replicate (n+1) z ++ x :: xs) =
      x :: (List.replicate (n+1) z ++ xs) := by
  unfold leftMacro
  rw [run_append, run_append]
  rw [← replicate_append_one n z, List.append_assoc, rotate_left_block]
  simp only [run_append, run, step, swap, List.cons_append]
  change run (rx n) (x :: ((z :: xs) ++ List.replicate n z)) = _
  rw [rx_transfer]
  simp [List.append_assoc]

theorem exchange_right_block (n : Nat) (z x : α) (xs : List α) :
    run (rightMacro n) (x :: (List.replicate (n+1) z ++ xs)) =
      List.replicate (n+1) z ++ x :: xs := by
  unfold rightMacro
  rw [run_append, run_append]
  change run (List.replicate n Op.R) (run (lx n) (z :: x :: (List.replicate n z ++ xs))) = _
  rw [lx_transfer]
  change run (List.replicate n Op.R) ((z :: x :: xs) ++ List.replicate n z) = _
  rw [rotate_right_block, ← replicate_append_one n z]
  simp [List.append_assoc]

theorem rx_length (n : Nat) : (rx n).length = 2*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rx, List.length_append, List.length_cons, List.length_nil, ih]; omega

theorem lx_length (n : Nat) : (lx n).length = 2*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [lx, List.length_append, List.length_cons, List.length_nil, ih]; omega

theorem left_macro_length (n : Nat) : (leftMacro n).length = 3*n+1 := by
  simp only [leftMacro, List.length_append, List.length_replicate, List.length_cons, List.length_nil, rx_length]
  omega

theorem right_macro_length (n : Nat) : (rightMacro n).length = 3*n+1 := by
  simp only [rightMacro, List.length_append, List.length_replicate, List.length_cons, List.length_nil, lx_length]
  omega

inductive Atom (β : Type*) where
  | named (value : β)
  | block (index : Nat)

def atomExpand (z : α) (extra : Nat → Nat) : Atom α → List α
  | .named x => [x]
  | .block j => List.replicate (extra j + 1) z

def expand (z : α) (extra : Nat → Nat) : List (Atom α) → List α
  | [] => []
  | a :: atoms => atomExpand z extra a ++ expand z extra atoms

theorem expand_append (z : α) (extra : Nat → Nat) (u v : List (Atom α)) :
    expand z extra (u ++ v) = expand z extra u ++ expand z extra v := by
  induction u with
  | nil => simp [expand]
  | cons a atoms ih => simp [expand, ih, List.append_assoc]

theorem replicate_add_blocks (u v : Nat) (z : α) :
    List.replicate (u+v) z = List.replicate u z ++ List.replicate v z := by
  induction u with
  | zero => simp
  | succ u ih => simpa [Nat.succ_add, List.replicate_succ] using congrArg (List.cons z) ih

theorem repeated_blocks_commute (u v : Nat) (z : α) :
    List.replicate u z ++ List.replicate v z = List.replicate v z ++ List.replicate u z := by
  rw [← replicate_add_blocks, ← replicate_add_blocks, Nat.add_comm u v]

def macroFor (extra : Nat → Nat) : Op → List (Atom α) → List Op
  | .L, .named _ :: _ => [Op.L]
  | .L, .block j :: _ => List.replicate (extra j + 1) Op.L
  | .R, atoms => match atoms.reverse with
    | .named _ :: _ => [Op.R]
    | .block j :: _ => List.replicate (extra j + 1) Op.R
    | [] => []
  | .X, .named _ :: .named _ :: _ => [Op.X]
  | .X, .block j :: .named _ :: _ => leftMacro (extra j)
  | .X, .named _ :: .block j :: _ => rightMacro (extra j)
  | _, _ => []

/- The block/block branch is identity on expanded zeros. Concrete audited
   direct profiles exclude such base exchanges, so agree with their strict
   implementation on the entire certified domain. -/
theorem run_macro (z : α) (extra : Nat → Nat) (op : Op) (atoms : List (Atom α)) :
    run (macroFor extra op atoms) (expand z extra atoms) = expand z extra (step op atoms) := by
  cases op with
  | L =>
    cases atoms with
    | nil => simp [macroFor, expand, run, step, left]
    | cons a atoms =>
      cases a with
      | named x => simp [macroFor, expand, atomExpand, run, step, left, expand_append]
      | block j =>
        simpa [macroFor, expand, atomExpand, step, left, expand_append] using
          rotate_left_block (extra j + 1) z (expand z extra atoms)
  | R =>
    cases h : atoms.reverse with
    | nil =>
      have hs : atoms = [] := by simpa using congrArg List.reverse h
      subst atoms
      simp [macroFor, expand, run, step, right, left]
    | cons a atoms' =>
      have hs : atoms = atoms'.reverse ++ [a] := by simpa using congrArg List.reverse h
      rw [hs]
      cases a with
      | named x => simp [macroFor, expand_append, expand, atomExpand, run, step, right_append]
      | block j =>
        simpa [macroFor, expand_append, expand, atomExpand, step, right_append] using
          rotate_right_block (extra j + 1) z (expand z extra atoms'.reverse)
  | X =>
    cases atoms with
    | nil => simp [macroFor, expand, run, step, swap]
    | cons a atoms =>
      cases atoms with
      | nil => cases a <;> simp [macroFor, expand, run, step, swap]
      | cons b atoms =>
        cases a with
        | named x =>
          cases b with
          | named y => simp [macroFor, expand, atomExpand, run, step, swap]
          | block j =>
            simpa [macroFor, expand, atomExpand, step, swap] using
              exchange_right_block (extra j) z x (expand z extra atoms)
        | block j =>
          cases b with
          | named x =>
            simpa [macroFor, expand, atomExpand, step, swap] using
              exchange_left_block (extra j) z x (expand z extra atoms)
          | block h =>
            simp only [macroFor, expand, atomExpand, run, step, swap]
            rw [← List.append_assoc, repeated_blocks_commute]
            simp only [List.append_assoc]

def liftWord (extra : Nat → Nat) : List Op → List (Atom α) → List Op
  | [], _ => []
  | op :: ops, atoms => macroFor extra op atoms ++ liftWord extra ops (step op atoms)

theorem run_liftWord (z : α) (extra : Nat → Nat) (ops : List Op) (atoms : List (Atom α)) :
    run (liftWord extra ops atoms) (expand z extra atoms) = expand z extra (run ops atoms) := by
  induction ops generalizing atoms with
  | nil => rfl
  | cons op ops ih =>
    rw [liftWord, run_append, run_macro]
    simpa only [run] using ih (step op atoms)

def macroPrice (extra : Nat → Nat) : Op → List (Atom α) → Nat
  | .L, .named _ :: _ => 1
  | .L, .block j :: _ => extra j + 1
  | .R, atoms => match atoms.reverse with
    | .named _ :: _ => 1
    | .block j :: _ => extra j + 1
    | [] => 0
  | .X, .named _ :: .named _ :: _ => 1
  | .X, .block j :: .named _ :: _ => 3 * extra j + 1
  | .X, .named _ :: .block j :: _ => 3 * extra j + 1
  | _, _ => 0

theorem macro_length_eq_price (extra : Nat → Nat) (op : Op) (atoms : List (Atom α)) :
    (macroFor extra op atoms).length = macroPrice extra op atoms := by
  cases op with
  | L =>
    cases atoms with
    | nil => simp [macroFor, macroPrice]
    | cons a atoms => cases a <;> simp [macroFor, macroPrice]
  | R =>
    cases h : atoms.reverse with
    | nil => simp [macroFor, macroPrice, h]
    | cons a atoms => cases a <;> simp [macroFor, macroPrice, h]
  | X =>
    cases atoms with
    | nil => simp [macroFor, macroPrice]
    | cons a atoms =>
      cases atoms with
      | nil => cases a <;> simp [macroFor, macroPrice]
      | cons b atoms =>
        cases a <;> cases b <;>
          simp [macroFor, macroPrice, left_macro_length, right_macro_length]

def rawPrice (extra : Nat → Nat) : List Op → List (Atom α) → Nat
  | [], _ => 0
  | op :: ops, atoms => macroPrice extra op atoms + rawPrice extra ops (step op atoms)

theorem lifted_word_length (extra : Nat → Nat) (ops : List Op) (atoms : List (Atom α)) :
    (liftWord extra ops atoms).length = rawPrice extra ops atoms := by
  induction ops generalizing atoms with
  | nil => rfl
  | cons op ops ih => simp [liftWord, rawPrice, macro_length_eq_price, ih]

#print axioms macro_length_eq_price
#print axioms lifted_word_length

#print axioms run_macro
#print axioms run_liftWord

#print axioms exchange_left_block
#print axioms exchange_right_block
#print axioms left_macro_length
#print axioms right_macro_length

#print axioms rotate_left_block
#print axioms rotate_right_block
end LRX.BlockExchange
