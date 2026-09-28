import Init

set_option Elab.async false

namespace Astra3Block

inductive Op where
  | L | R | X
  deriving DecidableEq, Repr

def left (xs : List α) : List α :=
  match xs with
  | [] => []
  | x :: tail => tail ++ [x]

def right (xs : List α) : List α := (left xs.reverse).reverse

def swap (xs : List α) : List α :=
  match xs with
  | x :: y :: tail => y :: x :: tail
  | _ => xs

def step (op : Op) (xs : List α) : List α :=
  match op with
  | .L => left xs
  | .R => right xs
  | .X => swap xs

def run (word : List Op) (xs : List α) : List α :=
  match word with
  | [] => xs
  | op :: rest => run rest (step op xs)

theorem run_append (u v : List Op) (xs : List α) :
    run (u ++ v) xs = run v (run u xs) := by
  induction u generalizing xs with
  | nil => rfl
  | cons op u ih => simp [run, ih]

theorem right_left (xs : List α) : right (left xs) = xs := by
  cases xs with
  | nil => rfl
  | cons x tail => simp [left, right, List.reverse_append]

theorem right_append (xs : List α) (z : α) :
    right (xs ++ [z]) = z :: xs := by
  simp [right, List.reverse_append, left]

def lefts : Nat → List α → List α
  | 0, xs => xs
  | n+1, xs => lefts n (left xs)

def rights : Nat → List α → List α
  | 0, xs => xs
  | n+1, xs => right (rights n xs)

theorem cancel_powers (n : Nat) (xs : List α) :
    rights n (lefts n xs) = xs := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => simp [rights, lefts, ih, right_left]

def lxSteps : Nat → List α → List α
  | 0, xs => xs
  | n+1, xs => lxSteps n (swap (left xs))

theorem bubble (bs tail : List α) (a z : α) :
    lxSteps bs.length (a :: z :: (bs ++ tail)) =
      lefts bs.length ((a :: bs) ++ z :: tail) := by
  induction bs generalizing a tail with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, lxSteps, lefts]
    simpa [left, swap, List.append_assoc] using ih (tail ++ [a]) b

def lxWord : Nat → List Op
  | 0 => []
  | n+1 => [.L, .X] ++ lxWord n

def rightWord : Nat → List Op
  | 0 => []
  | n+1 => rightWord n ++ [.R]

theorem run_lx (n : Nat) (xs : List α) : run (lxWord n) xs = lxSteps n xs := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => simp [lxWord, run_append, run, step, lxSteps, ih]

theorem run_rights (n : Nat) (xs : List α) : run (rightWord n) xs = rights n xs := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => simp [rightWord, run_append, run, step, rights, ih]

def blockLeftWord (k : Nat) : List Op := [.R, .X] ++ lxWord (k-1) ++ rightWord (k-1)

/- This is the literal RX(LX)^(k-1)R^(k-1) word, acting on the VISIBLE
   vector. It moves the final symbol z to immediately after a nonempty block;
   in the LRX application z=0. All cursor changes are actual L/R letters. -/
theorem block_left (a z : α) (bs tail : List α) :
    run (blockLeftWord (bs.length+1)) ((a :: bs) ++ tail ++ [z]) =
      (a :: bs) ++ z :: tail := by
  simp only [blockLeftWord, Nat.add_sub_cancel, run_append, run_lx, run_rights]
  simp only [run, step, right_append, swap]
  change rights bs.length (lxSteps bs.length (a :: z :: (bs ++ tail))) =
    (a :: bs) ++ z :: tail
  rw [bubble, cancel_powers]

theorem lx_length (n : Nat) : (lxWord n).length = 2*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [lxWord, ih]; omega

theorem right_length (n : Nat) : (rightWord n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rightWord, ih]

theorem block_left_cost (k : Nat) (nonempty : 1 ≤ k) :
    (blockLeftWord k).length = 3*k-1 := by
  simp [blockLeftWord, lx_length, right_length]
  omega

def repeatWord (word : List Op) : Nat → List Op
  | 0 => []
  | n+1 => word ++ repeatWord word n

theorem repeat_length (word : List Op) (n : Nat) :
    (repeatWord word n).length = n * word.length := by
  induction n with
  | zero => simp [repeatWord]
  | succ n ih => simp [repeatWord, ih, Nat.succ_mul, Nat.add_comm]

theorem block_left_gap (a z : α) (bs tail : List α) (r : Nat) :
    run (repeatWord (blockLeftWord (bs.length+1)) r)
      ((a :: bs) ++ tail ++ List.replicate r z) =
      (a :: bs) ++ List.replicate r z ++ tail := by
  induction r generalizing tail with
  | zero => simp [repeatWord, run]
  | succ r ih =>
    rw [repeatWord, run_append, List.replicate_succ']
    have first : run (blockLeftWord (bs.length+1))
        ((a :: bs) ++ tail ++ (List.replicate r z ++ [z])) =
        (a :: bs) ++ (z :: tail) ++ List.replicate r z := by
      simpa [List.append_assoc] using block_left a z bs (tail ++ List.replicate r z)
    rw [first, ih]
    simp [List.append_assoc]

theorem lefts_append (front suffix : List α) :
    lefts front.length (front ++ suffix) = suffix ++ front := by
  induction front generalizing suffix with
  | nil => simp [lefts]
  | cons a front ih =>
    simpa [lefts, left, List.append_assoc] using ih (suffix ++ [a])

theorem rights_append (front suffix : List α) :
    rights suffix.length (front ++ suffix) = suffix ++ front := by
  rw [← lefts_append suffix front, cancel_powers]

def gapRepairWord (k r suffixLength : Nat) : List Op :=
  repeatWord (blockLeftWord k) r ++ rightWord suffixLength

/- Fully paid gap repair. For A=[h,...,m], B=[1,...,h-1], z=0, this
   maps the pivot-sorted visible state [A,B,0^r] to [B,A,0^r]=v0.
   The final rotation uses |B| letters, not a free cyclic quotient. -/
theorem gap_repair (a z : α) (bs suffix : List α) (r : Nat) :
    run (gapRepairWord (bs.length+1) r suffix.length)
      ((a :: bs) ++ suffix ++ List.replicate r z) =
      suffix ++ (a :: bs) ++ List.replicate r z := by
  simp only [gapRepairWord, run_append, block_left_gap, run_rights]
  rw [rights_append]
  simp [List.append_assoc]

theorem gap_repair_cost (k r suffixLength : Nat) (nonempty : 1 ≤ k) :
    (gapRepairWord k r suffixLength).length = r * (3*k-1) + suffixLength := by
  simp [gapRepairWord, repeat_length, block_left_cost k nonempty, right_length]

end Astra3Block

#print axioms Astra3Block.block_left
#print axioms Astra3Block.block_left_cost
#print axioms Astra3Block.block_left_gap
#print axioms Astra3Block.gap_repair
#print axioms Astra3Block.gap_repair_cost
