import BlockTransportRight
set_option Elab.async false

namespace Astra3Block

def attachRightWord (k gap : Nat) : List Op :=
  repeatWord (blockRightWord k) gap ++ [.L]

theorem attach_right (a b z : α) (bs tail : List α) (gap : Nat) :
    run (attachRightWord (bs.length+1) gap)
      (a :: (List.replicate gap z ++ b :: tail ++ bs)) =
      b :: (tail ++ List.replicate gap z ++ bs ++ [a]) := by
  simp only [attachRightWord, run_append]
  rw [block_right_gap]
  simp [run, step, left, List.append_assoc]

def spaced (z : α) : List (Nat × α) → List α
  | [] => []
  | (gap, token) :: rest => List.replicate gap z ++ token :: spaced z rest

def growingRightWord (k : Nat) : List (Nat × α) → List Op
  | [] => []
  | (gap, _) :: rest => attachRightWord k gap ++ growingRightWord (k+1) rest

def growingCost (k : Nat) : List (Nat × α) → Nat
  | [] => 0
  | (gap, _) :: rest => gap*(3*k-1)+1+growingCost (k+1) rest

/- No Valid-plan premise: the word is explicitly constructed from arbitrary
   gap/token data. Initially bs++[a] is the growing block, cursor on a;
   the next tokens and zero gaps are in spaced. Finally every gap is behind
   the packed block, whose order is bs++[a]++tokens and cursor at its last
   token. Exterior tail is preserved. -/
theorem growing_right (a z : α) (bs tail : List α) (items : List (Nat × α)) :
    run (growingRightWord (bs.length+1) items)
      (a :: (spaced z items ++ tail ++ bs)) =
      (a :: items.map Prod.snd).getLast (by simp) ::
        (tail ++ List.replicate (items.map Prod.fst).sum z ++ bs ++
          (a :: items.map Prod.snd).dropLast) := by
  induction items generalizing a bs tail with
  | nil => simp [growingRightWord, spaced, run]
  | cons item items ih =>
    rcases item with ⟨gap, b⟩
    simp only [growingRightWord, run_append, spaced]
    have first : run (attachRightWord (bs.length+1) gap)
        (a :: ((List.replicate gap z ++ b :: spaced z items) ++ tail ++ bs)) =
        b :: (spaced z items ++ (tail ++ List.replicate gap z) ++ (bs ++ [a])) := by
      simpa [List.append_assoc] using attach_right a b z bs (spaced z items ++ tail) gap
    rw [first]
    have h := ih b (bs ++ [a]) (tail ++ List.replicate gap z)
    simpa [List.length_append, List.getLast_cons, List.dropLast_cons₂,
      List.append_assoc, List.replicate_append_replicate] using h

theorem growing_right_cost (k : Nat) (items : List (Nat × α)) (hk : 1 ≤ k) :
    (growingRightWord k items).length = growingCost k items := by
  induction items generalizing k with
  | nil => rfl
  | cons item items ih =>
    rcases item with ⟨gap, b⟩
    have hk' : 1 ≤ k+1 := by omega
    simp [growingRightWord, growingCost, attachRightWord, repeat_length,
      block_right_cost k hk, ih (k+1) hk', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def attachLeftWord (k gap : Nat) : List Op :=
  repeatWord (blockLeftWord k) gap ++ [.R]

theorem attach_left (a b z : α) (bs tail : List α) (gap : Nat) :
    run (attachLeftWord (bs.length+1) gap)
      ((a :: bs) ++ tail ++ [b] ++ List.replicate gap z) =
      b :: ((a :: bs) ++ List.replicate gap z ++ tail) := by
  simp only [attachLeftWord, run_append]
  have h := block_left_gap a z bs (tail ++ [b]) gap
  have first : run (repeatWord (blockLeftWord (bs.length+1)) gap)
      ((a :: bs) ++ tail ++ [b] ++ List.replicate gap z) =
      ((a :: bs) ++ List.replicate gap z ++ tail) ++ [b] := by
    simpa [List.append_assoc] using h
  rw [first]
  change right (((a :: bs) ++ List.replicate gap z ++ tail) ++ [b]) =
    b :: ((a :: bs) ++ List.replicate gap z ++ tail)
  exact right_append _ b

def spacedLeft (z : α) : List (Nat × α) → List α
  | [] => []
  | (gap, token) :: rest => spacedLeft z rest ++ [token] ++ List.replicate gap z

def growingLeftWord (k : Nat) : List (Nat × α) → List Op
  | [] => []
  | (gap, _) :: rest => attachLeftWord k gap ++ growingLeftWord (k+1) rest

/- Items are listed in encounter order moving LEFT. The final packed block
   therefore has their tokens in reverse encounter order before the old block.
   No reflection of operations or uncharged change of orientation is used. -/
theorem growing_left (a z : α) (bs tail : List α) (items : List (Nat × α)) :
    run (growingLeftWord (bs.length+1) items)
      ((a :: bs) ++ tail ++ spacedLeft z items) =
      (items.map Prod.snd).reverse ++ (a :: bs) ++
        List.replicate (items.map Prod.fst).sum z ++ tail := by
  induction items generalizing a bs tail with
  | nil => simp [growingLeftWord, spacedLeft, run]
  | cons item items ih =>
    rcases item with ⟨gap, b⟩
    simp only [growingLeftWord, run_append, spacedLeft]
    have first : run (attachLeftWord (bs.length+1) gap)
        ((a :: bs) ++ tail ++ (spacedLeft z items ++ [b] ++ List.replicate gap z)) =
        (b :: a :: bs) ++ (List.replicate gap z ++ tail) ++ spacedLeft z items := by
      simpa [List.append_assoc] using attach_left a b z bs (tail ++ spacedLeft z items) gap
    rw [first]
    have h := ih b (a :: bs) (List.replicate gap z ++ tail)
    have zeros : List.replicate (items.map Prod.fst).sum z ++
        (List.replicate gap z ++ tail) =
        List.replicate (gap + (items.map Prod.fst).sum) z ++ tail := by
      rw [← List.append_assoc, List.replicate_append_replicate, Nat.add_comm]
    simpa [List.reverse_cons, List.append_assoc, zeros] using h

theorem growing_left_cost (k : Nat) (items : List (Nat × α)) (hk : 1 ≤ k) :
    (growingLeftWord k items).length = growingCost k items := by
  induction items generalizing k with
  | nil => rfl
  | cons item items ih =>
    rcases item with ⟨gap, b⟩
    have hk' : 1 ≤ k+1 := by omega
    simp [growingLeftWord, growingCost, attachLeftWord, repeat_length,
      block_left_cost k hk, ih (k+1) hk', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def mergeBlocksWord (rightSize gap leftSize : Nat) : List Op :=
  repeatWord (blockLeftWord rightSize) gap ++ rightWord leftSize

/- Cursor starts at first token b of the right block. The left block lies
   immediately before the central zero gap. Output cursor is at the beginning
   of the merged left++right block; the leftSize R letters are charged. -/
theorem merge_blocks (b z : α) (bs leftBlock tail : List α) (gap : Nat) :
    run (mergeBlocksWord (bs.length+1) gap leftBlock.length)
      ((b :: bs) ++ tail ++ leftBlock ++ List.replicate gap z) =
      leftBlock ++ (b :: bs) ++ List.replicate gap z ++ tail := by
  simp only [mergeBlocksWord, run_append, run_rights]
  have h := block_left_gap b z bs (tail ++ leftBlock) gap
  have first : run (repeatWord (blockLeftWord (bs.length+1)) gap)
      ((b :: bs) ++ tail ++ leftBlock ++ List.replicate gap z) =
      ((b :: bs) ++ List.replicate gap z ++ tail) ++ leftBlock := by
    simpa [List.append_assoc] using h
  rw [first, rights_append]
  simp [List.append_assoc]

theorem merge_blocks_cost (rightSize gap leftSize : Nat) (hk : 1 ≤ rightSize) :
    (mergeBlocksWord rightSize gap leftSize).length =
      gap*(3*rightSize-1)+leftSize := by
  simp [mergeBlocksWord, repeat_length, block_left_cost rightSize hk, right_length]

end Astra3Block

#print axioms Astra3Block.growing_right
#print axioms Astra3Block.growing_right_cost
#print axioms Astra3Block.growing_left
#print axioms Astra3Block.growing_left_cost
#print axioms Astra3Block.merge_blocks
#print axioms Astra3Block.merge_blocks_cost
