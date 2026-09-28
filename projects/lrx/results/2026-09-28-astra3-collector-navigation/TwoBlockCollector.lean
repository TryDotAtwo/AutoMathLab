import GrowingCollector
set_option Elab.async false

namespace Astra3Block

def approachWord (forward backward : Nat) : List Op :=
  if forward ≤ backward then leftWord forward else rightWord backward

theorem approach_cut (front back : List α) :
    run (approachWord front.length back.length) (front ++ back) = back ++ front := by
  unfold approachWord
  split
  · rw [run_lefts, lefts_append]
  · rw [run_rights, rights_append]

theorem approach_cost (forward backward : Nat) :
    (approachWord forward backward).length = min forward backward := by
  unfold approachWord
  split
  · next h => rw [left_length, Nat.min_eq_left h]
  · next h => rw [right_length, Nat.min_eq_right (show backward ≤ forward by omega)]

theorem rejoin_last (xs tail : List α) (h : xs ≠ []) :
    xs.dropLast ++ (xs.getLast h :: tail) = xs ++ tail := by
  have hr := List.dropLast_concat_getLast h
  calc
    xs.dropLast ++ (xs.getLast h :: tail) = (xs.dropLast ++ [xs.getLast h]) ++ tail := by
      simp [List.append_assoc]
    _ = xs ++ tail := congrArg (fun ys => ys ++ tail) hr

def firstArc (z : α) (vitems : List (Nat × α)) (central : Nat) : Nat :=
  1 + central + (spacedLeft z vitems).length

def secondArc (uitems : List (Nat × α)) (cut : Nat) : Nat :=
  1 + cut + (uitems.map Prod.fst).sum + uitems.length

def twoBlockWord (z : α) (uitems vitems : List (Nat × α)) (central cut : Nat) : List Op :=
  growingRightWord 1 uitems ++
  approachWord (firstArc z vitems central) (secondArc uitems cut) ++
  growingLeftWord 1 vitems ++
  mergeBlocksWord (vitems.length+1) central (uitems.length+1)

/- Complete collector for a chosen cut, with both nonempty token groups.
   Cursor starts at u0. Initial physical order:
   u0, right-encountered U-items, central zero gap,
   left-encountered V-items (in reverse), vLast, cut zero gap.
   Final visible order U++V is packed, cursor at its FIRST token.
   The inter-pass shortest rotation is an actual word, not a phase quotient. -/
theorem two_block_collect (u0 vLast z : α) (uitems vitems : List (Nat × α))
    (central cut : Nat) :
    run (twoBlockWord z uitems vitems central cut)
      (u0 :: (spaced z uitems ++ List.replicate central z ++
        spacedLeft z vitems ++ [vLast] ++ List.replicate cut z)) =
      (u0 :: uitems.map Prod.snd) ++ (vitems.map Prod.snd).reverse ++ [vLast] ++
        List.replicate (central + ((vitems.map Prod.fst).sum + cut +
          (uitems.map Prod.fst).sum)) z := by
  let U := u0 :: uitems.map Prod.snd
  let V := (vitems.map Prod.snd).reverse ++ [vLast]
  have hUnil : U ≠ [] := by simp [U]
  have hVnil : V ≠ [] := by simp [V]
  let uLast := U.getLast hUnil
  let uBefore := U.dropLast
  let front := [uLast] ++ List.replicate central z ++ spacedLeft z vitems
  let back := [vLast] ++ List.replicate cut z ++
    List.replicate (uitems.map Prod.fst).sum z ++ uBefore
  let outside := List.replicate ((vitems.map Prod.fst).sum + cut +
    (uitems.map Prod.fst).sum) z
  have hfront : front.length = firstArc z vitems central := by
    simp [front, firstArc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hback : back.length = secondArc uitems cut := by
    simp [back, uBefore, U, secondArc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hUlen : U.length = uitems.length+1 := by simp [U]
  have hU : run (growingRightWord 1 uitems)
      (u0 :: (spaced z uitems ++ List.replicate central z ++
        spacedLeft z vitems ++ [vLast] ++ List.replicate cut z)) = front ++ back := by
    simpa [front, back, uLast, uBefore, U, ← List.replicate_append_replicate,
      List.append_assoc] using
      growing_right u0 z []
        (List.replicate central z ++ spacedLeft z vitems ++ [vLast] ++
          List.replicate cut z) uitems
  have hApproach : run (approachWord (firstArc z vitems central)
      (secondArc uitems cut)) (front ++ back) = back ++ front := by
    rw [← hfront, ← hback, approach_cut]
  have hV : run (growingLeftWord 1 vitems) (back ++ front) =
      V ++ outside ++ U ++ List.replicate central z := by
    have joinTail (tail : List α) : uBefore ++ (uLast :: tail) = U ++ tail :=
      rejoin_last U tail hUnil
    have h := growing_left vLast z []
      (List.replicate cut z ++ List.replicate (uitems.map Prod.fst).sum z ++
        U ++ List.replicate central z) vitems
    simpa [back, front, V, outside, ← List.replicate_append_replicate,
      List.append_assoc, joinTail] using h
  obtain ⟨b, bs, hVB⟩ := List.exists_cons_of_ne_nil hVnil
  have hVlen : bs.length+1 = vitems.length+1 := by
    have h := congrArg List.length hVB
    simp [V] at h
    omega
  have hMerge : run (mergeBlocksWord (vitems.length+1) central (uitems.length+1))
      (V ++ outside ++ U ++ List.replicate central z) =
      U ++ V ++ List.replicate central z ++ outside := by
    simpa only [hVlen, hUlen, ← hVB] using merge_blocks b z bs U outside central
  simp only [twoBlockWord, run_append]
  rw [hU, hApproach, hV, hMerge]
  simp [U, V, outside, List.append_assoc, ← List.replicate_append_replicate]

theorem two_block_cost (z : α) (uitems vitems : List (Nat × α)) (central cut : Nat) :
    (twoBlockWord z uitems vitems central cut).length =
      growingCost 1 uitems +
      min (firstArc z vitems central) (secondArc uitems cut) +
      growingCost 1 vitems + central*(3*(vitems.length+1)-1)+(uitems.length+1) := by
  have hk : 1 ≤ vitems.length+1 := by omega
  simp [twoBlockWord, growing_right_cost 1 uitems (by decide),
    growing_left_cost 1 vitems (by decide), approach_cost,
    merge_blocks_cost (vitems.length+1) central (uitems.length+1) hk, Nat.add_assoc]

theorem left_right (xs : List α) : left (right xs) = xs := by
  have h := congrArg List.reverse (right_left xs.reverse)
  simpa [right] using h

theorem cancel_right_powers (n : Nat) (xs : List α) : lefts n (rights n xs) = xs := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => simp [lefts, rights, left_right, ih]

def twoBlockCoreWord (z : α) (uitems vitems : List (Nat × α)) (central cut : Nat) : List Op :=
  growingRightWord 1 uitems ++
  approachWord (firstArc z vitems central) (secondArc uitems cut) ++
  growingLeftWord 1 vitems ++
  repeatWord (blockLeftWord (vitems.length+1)) central

/- The cocktail improvement deliberately omits the final return R^|U|.
   This theorem records its ACTUAL terminal cursor: offset |U| inside the
   packed block. `lefts` here describes the resulting visible list; no extra
   uncharged operation is appended to the constructed core word. -/
theorem two_block_core_collect (u0 vLast z : α) (uitems vitems : List (Nat × α))
    (central cut : Nat) :
    run (twoBlockCoreWord z uitems vitems central cut)
      (u0 :: (spaced z uitems ++ List.replicate central z ++
        spacedLeft z vitems ++ [vLast] ++ List.replicate cut z)) =
      lefts (uitems.length+1)
        ((u0 :: uitems.map Prod.snd) ++ (vitems.map Prod.snd).reverse ++ [vLast] ++
          List.replicate (central + ((vitems.map Prod.fst).sum + cut +
            (uitems.map Prod.fst).sum)) z) := by
  have h := two_block_collect u0 vLast z uitems vitems central cut
  have joined : twoBlockWord z uitems vitems central cut =
      twoBlockCoreWord z uitems vitems central cut ++ rightWord (uitems.length+1) := by
    simp [twoBlockWord, twoBlockCoreWord, mergeBlocksWord, List.append_assoc]
  rw [joined, run_append, run_rights] at h
  have h' := congrArg (lefts (uitems.length+1)) h
  rw [cancel_right_powers] at h'
  exact h'

theorem two_block_core_cost (z : α) (uitems vitems : List (Nat × α)) (central cut : Nat) :
    (twoBlockCoreWord z uitems vitems central cut).length =
      growingCost 1 uitems +
      min (firstArc z vitems central) (secondArc uitems cut) +
      growingCost 1 vitems + central*(3*(vitems.length+1)-1) := by
  have hk : 1 ≤ vitems.length+1 := by omega
  simp [twoBlockCoreWord, growing_right_cost 1 uitems (by decide),
    growing_left_cost 1 vitems (by decide), approach_cost, repeat_length,
    block_left_cost (vitems.length+1) hk, Nat.add_assoc]

end Astra3Block

#print axioms Astra3Block.two_block_collect
#print axioms Astra3Block.two_block_cost
#print axioms Astra3Block.two_block_core_collect
#print axioms Astra3Block.two_block_core_cost
