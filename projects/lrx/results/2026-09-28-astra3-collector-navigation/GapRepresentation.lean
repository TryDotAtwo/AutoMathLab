import TwoBlockCollector
import Navigation
set_option Elab.async false

namespace Astra3Block

def gapParse [DecidableEq α] (z : α) : List α → List (Nat × α) × Nat
  | [] => ([], 0)
  | x :: xs =>
    let parsed := gapParse z xs
    if x = z then
      match parsed.1 with
      | [] => ([], parsed.2+1)
      | (gap, token) :: rest => ((gap+1, token) :: rest, parsed.2)
    else ((0, x) :: parsed.1, parsed.2)

theorem gap_parse_reconstruct [DecidableEq α] (z : α) (xs : List α) :
    spaced z (gapParse z xs).1 ++ List.replicate (gapParse z xs).2 z = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : gapParse z xs with
    | mk items trailing =>
      simp only [h, Prod.fst, Prod.snd] at ih
      by_cases hx : x = z
      · subst x
        cases items with
        | nil =>
          simpa [gapParse, h, spaced, List.replicate_succ] using congrArg (List.cons z) ih
        | cons item items =>
          rcases item with ⟨gap, token⟩
          simpa [gapParse, h, spaced, List.replicate_succ, List.append_assoc] using congrArg (List.cons z) ih
      · simpa [gapParse, h, hx, spaced] using congrArg (List.cons x) ih

theorem gap_parse_labels [DecidableEq α] (z : α) (xs : List α) :
    (gapParse z xs).1.map Prod.snd = xs.filter (fun x => decide (x ≠ z)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : gapParse z xs with
    | mk items trailing =>
      simp only [h, Prod.fst, Prod.snd] at ih
      by_cases hx : x = z
      · subst x
        cases items with
        | nil => simpa only [gapParse, h, if_pos rfl, Prod.fst, Prod.snd,
            List.map_nil, List.filter_cons, ne_eq, not_true_eq_false,
            decide_false, Bool.false_eq_true, if_false] using ih
        | cons item items =>
          rcases item with ⟨gap, token⟩
          simpa only [gapParse, h, if_pos rfl, Prod.fst, Prod.snd,
            List.map_cons, List.filter_cons, ne_eq, not_true_eq_false,
            decide_false, Bool.false_eq_true, if_false] using ih
      · simpa only [gapParse, h, if_neg hx, Prod.fst, Prod.snd,
          List.map_cons, List.filter_cons, if_pos (decide_eq_true_iff.mpr hx)]
          using congrArg (List.cons x) ih

/- A cut is executed by an actual shortest rotation. Parsing is only a
   representation of the resulting list, not a hidden physical operation. -/
theorem cut_and_parse [DecidableEq α] (token z : α) (front back : List α) :
    run (approachWord front.length (back.length+1)) (front ++ token :: back) =
      token :: (spaced z (gapParse z (back ++ front)).1 ++
        List.replicate (gapParse z (back ++ front)).2 z) := by
  have h := approach_cut front (token :: back)
  have parsed := gap_parse_reconstruct z (back ++ front)
  simpa [parsed] using h

theorem cut_cost_modular [DecidableEq α] (token : α) (front back : List α) :
    (approachWord front.length (back.length+1)).length =
      Astra3Navigation.distance (front ++ token :: back).length 0 front.length := by
  rw [approach_cost]
  unfold Astra3Navigation.distance Astra3Navigation.linearDistance
  simp only [Nat.zero_le, if_true, Nat.sub_zero]
  have h : (front ++ token :: back).length - front.length = back.length+1 := by
    simp only [List.length_append, List.length_cons]
    omega
  rw [h]

/- Every selected member supplies its own real cut and gap representation.
   This does not yet split the parsed token list into the two balanced groups
   required by the collector, nor average over all selected members. -/
theorem selected_cut_exists [DecidableEq α] (z token : α) (xs : List α)
    (present : token ∈ xs) :
    ∃ (word : List Op) (items : List (Nat × α)) (trailing : Nat),
      run word xs = token :: (spaced z items ++ List.replicate trailing z) ∧
      2*word.length ≤ xs.length := by
  obtain ⟨front, back, hx⟩ := List.mem_iff_append.mp present
  subst xs
  refine ⟨approachWord front.length (back.length+1),
    (gapParse z (back ++ front)).1, (gapParse z (back ++ front)).2, ?_, ?_⟩
  · exact cut_and_parse token z front back
  · rw [approach_cost]
    simp only [List.length_append, List.length_cons]
    omega

theorem spaced_append (z : α) (xs ys : List (Nat × α)) :
    spaced z (xs ++ ys) = spaced z xs ++ spaced z ys := by
  induction xs with
  | nil => rfl
  | cons item xs ih =>
    rcases item with ⟨gap, token⟩
    simp [spaced, ih, List.append_assoc]

theorem spacedLeft_append (z : α) (xs ys : List (Nat × α)) :
    spacedLeft z (xs ++ ys) = spacedLeft z ys ++ spacedLeft z xs := by
  induction xs with
  | nil => simp [spacedLeft]
  | cons item xs ih =>
    rcases item with ⟨gap, token⟩
    simp [spacedLeft, ih, List.append_assoc]

/- Reindex the second group for the actual leftward encounter order.
   This is list equality, not a free rotation or a physical operation. -/
theorem left_encounter_exists (z token : α) (items : List (Nat × α)) :
    ∃ (revItems : List (Nat × α)) (last : α),
      token :: spaced z items = spacedLeft z revItems ++ [last] ∧
      revItems.length = items.length ∧
      (revItems.map Prod.snd).reverse ++ [last] = token :: items.map Prod.snd ∧
      (revItems.map Prod.fst).sum = (items.map Prod.fst).sum := by
  induction items generalizing token with
  | nil => exact ⟨[], token, rfl, rfl, rfl, rfl⟩
  | cons item items ih =>
    rcases item with ⟨gap, next⟩
    obtain ⟨revItems, last, hrep, hlen, hlabels, hgaps⟩ := ih next
    refine ⟨revItems ++ [(gap, token)], last, ?_, ?_, ?_, ?_⟩
    · simp [spaced, spacedLeft_append, spacedLeft, List.append_assoc, ← hrep]
    · simp [hlen]
    · simpa [List.reverse_append, List.append_assoc] using congrArg (List.cons token) hlabels
    · have sumLast (ns : List Nat) : (ns ++ [gap]).sum = ns.sum + gap := by
        induction ns with
        | nil => simp
        | cons n ns ih => simp [ih, Nat.add_assoc]
      simp [sumLast, hgaps, Nat.add_comm]

theorem prescribed_split_exists (items : List (Nat × α)) (k : Nat)
    (hk : k < items.length) :
    ∃ (uitems rest : List (Nat × α)) (gap : Nat) (token : α),
      items = uitems ++ (gap, token) :: rest ∧
      uitems.length = k ∧ rest.length + k + 1 = items.length := by
  have hne : items.drop k ≠ [] := by
    intro h
    have := List.drop_eq_nil_iff.mp h
    omega
  obtain ⟨item, rest, hdrop⟩ := List.exists_cons_of_ne_nil hne
  rcases item with ⟨gap, token⟩
  refine ⟨items.take k, rest, gap, token, ?_, ?_, ?_⟩
  · rw [← hdrop, List.take_append_drop]
  · simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  · have hl := congrArg List.length hdrop
    simp only [List.length_drop, List.length_cons] at hl
    omega

/- Arbitrary original input, any selected cut, any nonempty split of its
   remaining labels: a real paid word packs the labels in their cyclic order.
   No distinctness, nonzero premise, or sorting conclusion is smuggled in. -/
theorem parsed_cut_collect [DecidableEq α] (z token : α) (front back : List α)
    (uitems rest : List (Nat × α)) (central : Nat) (vfirst : α)
    (split : (gapParse z (back ++ front)).1 = uitems ++ (central, vfirst) :: rest) :
    ∃ (word : List Op) (vitems : List (Nat × α)),
      run word (front ++ token :: back) =
        lefts (uitems.length+1)
          ((token :: (gapParse z (back ++ front)).1.map Prod.snd) ++
            List.replicate ((uitems.map Prod.fst).sum + central +
              (rest.map Prod.fst).sum + (gapParse z (back ++ front)).2) z) ∧
      vitems.length = rest.length ∧
      word.length = min front.length (back.length+1) +
        growingCost 1 uitems +
        min (firstArc z vitems central)
          (secondArc uitems (gapParse z (back ++ front)).2) +
        growingCost 1 vitems + central*(3*(vitems.length+1)-1) := by
  obtain ⟨vitems, last, hrep, hlen, hlabels, hgaps⟩ := left_encounter_exists z vfirst rest
  refine ⟨approachWord front.length (back.length+1) ++
    twoBlockCoreWord z uitems vitems central (gapParse z (back ++ front)).2,
    vitems, ?_, hlen, ?_⟩
  · rw [run_append, cut_and_parse]
    have hinput : token :: (spaced z (gapParse z (back ++ front)).1 ++
        List.replicate (gapParse z (back ++ front)).2 z) =
        token :: (spaced z uitems ++ List.replicate central z ++
          spacedLeft z vitems ++ [last] ++ List.replicate (gapParse z (back ++ front)).2 z) := by
      simp [split, spaced_append, spaced, hrep, List.append_assoc]
    rw [hinput, two_block_core_collect]
    simp [split, List.append_assoc, hlabels, hgaps,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · rw [List.length_append, approach_cost, two_block_core_cost]
    omega

end Astra3Block

#print axioms Astra3Block.gap_parse_reconstruct
#print axioms Astra3Block.gap_parse_labels
#print axioms Astra3Block.cut_and_parse
#print axioms Astra3Block.cut_cost_modular
#print axioms Astra3Block.selected_cut_exists
#print axioms Astra3Block.spaced_append
#print axioms Astra3Block.spacedLeft_append
#print axioms Astra3Block.left_encounter_exists
#print axioms Astra3Block.prescribed_split_exists
#print axioms Astra3Block.parsed_cut_collect
