import BlockTransport
set_option Elab.async false

namespace Astra3Block

def rxSteps : Nat → List α → List α
  | 0, xs => xs
  | n+1, xs => rxSteps n (swap (right xs))

theorem bubble_reverse (bs tail : List α) (z : α) :
    rxSteps bs.length (z :: (tail ++ bs.reverse)) =
      z :: (bs.reverse ++ tail) := by
  induction bs generalizing tail with
  | nil => simp [rxSteps]
  | cons b bs ih =>
    simp only [List.length_cons, List.reverse_cons, rxSteps]
    have first : swap (right (z :: (tail ++ (bs.reverse ++ [b])))) =
        z :: ((b :: tail) ++ bs.reverse) := by
      have h := right_append (z :: (tail ++ bs.reverse)) b
      simpa [List.append_assoc, swap] using congrArg swap h
    rw [first, ih]
    simp [List.append_assoc]

theorem bubble_right (bs tail : List α) (z : α) :
    rxSteps bs.length (z :: (tail ++ bs)) = z :: (bs ++ tail) := by
  simpa using bubble_reverse bs.reverse tail z

def rxWord : Nat → List Op
  | 0 => []
  | n+1 => [.R, .X] ++ rxWord n

def leftWord : Nat → List Op
  | 0 => []
  | n+1 => [.L] ++ leftWord n

theorem run_rx (n : Nat) (xs : List α) : run (rxWord n) xs = rxSteps n xs := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => simp [rxWord, run_append, run, step, rxSteps, ih]

theorem run_lefts (n : Nat) (xs : List α) : run (leftWord n) xs = lefts n xs := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => simp [leftWord, run_append, run, step, lefts, ih]

def blockRightWord (k : Nat) : List Op := [.X] ++ rxWord (k-1) ++ leftWord k

/- The moving block is bs++[a], cursor on its last symbol a. In visible
   coordinates bs occurs at the END of the list. The next symbol z is crossed.
   The returned cursor is again on a, at the new last site of the moved block. -/
theorem block_right (a z : α) (bs tail : List α) :
    run (blockRightWord (bs.length+1)) (a :: z :: (tail ++ bs)) =
      a :: (tail ++ z :: bs) := by
  simp only [blockRightWord, Nat.add_sub_cancel, run_append, run_rx, run_lefts]
  simp only [run, step, swap]
  change lefts (bs.length+1) (rxSteps bs.length (z :: ((a :: tail) ++ bs))) =
    a :: (tail ++ z :: bs)
  rw [bubble_right]
  have h := lefts_append (z :: bs) (a :: tail)
  simpa using h

theorem rx_length (n : Nat) : (rxWord n).length = 2*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rxWord, ih]; omega

theorem left_length (n : Nat) : (leftWord n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [leftWord, ih]

theorem block_right_cost (k : Nat) (nonempty : 1 ≤ k) :
    (blockRightWord k).length = 3*k-1 := by
  simp [blockRightWord, rx_length, left_length]
  omega

theorem block_right_gap (a z : α) (bs tail : List α) (r : Nat) :
    run (repeatWord (blockRightWord (bs.length+1)) r)
      (a :: (List.replicate r z ++ tail ++ bs)) =
      a :: (tail ++ List.replicate r z ++ bs) := by
  induction r generalizing tail with
  | zero => simp [repeatWord, run]
  | succ r ih =>
    rw [repeatWord, run_append]
    simp only [List.replicate_succ, List.cons_append]
    have first : run (blockRightWord (bs.length+1))
        (a :: z :: (List.replicate r z ++ tail ++ bs)) =
        a :: (List.replicate r z ++ (tail ++ [z]) ++ bs) := by
      simpa [List.append_assoc] using block_right a z bs (List.replicate r z ++ tail)
    rw [first, ih]
    simp [List.append_assoc]

end Astra3Block

#print axioms Astra3Block.block_right
#print axioms Astra3Block.block_right_cost
#print axioms Astra3Block.block_right_gap
