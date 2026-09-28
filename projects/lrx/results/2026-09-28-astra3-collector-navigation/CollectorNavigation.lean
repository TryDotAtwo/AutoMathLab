import TwoBlockCollector
import Navigation
set_option Elab.async false

namespace Astra3Block

theorem spaced_length (z : α) (items : List (Nat × α)) :
    (spaced z items).length = items.length + (items.map Prod.fst).sum := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    rcases item with ⟨gap, token⟩
    simp [spaced, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem spacedLeft_length (z : α) (items : List (Nat × α)) :
    (spacedLeft z items).length = items.length + (items.map Prod.fst).sum := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    rcases item with ⟨gap, token⟩
    simp [spacedLeft, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def cutInput (u0 vLast z : α) (uitems vitems : List (Nat × α))
    (central cut : Nat) : List α :=
  u0 :: (spaced z uitems ++ List.replicate central z ++
    spacedLeft z vitems ++ [vLast] ++ List.replicate cut z)

def firstEndpoint (uitems : List (Nat × α)) : Nat :=
  uitems.length + (uitems.map Prod.fst).sum

theorem arcs_cover (u0 vLast z : α) (uitems vitems : List (Nat × α))
    (central cut : Nat) :
    firstArc z vitems central + secondArc uitems cut =
      (cutInput u0 vLast z uitems vitems central cut).length := by
  simp [firstArc, secondArc, cutInput, spaced_length, spacedLeft_length,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/- Actual original coordinates relative to the selected token cut:
   x is the last U-token site; y is the last V-token site. The collector
   proved in TwoBlockCollector ends each pass at these corresponding tokens. -/
theorem second_approach_exact (u0 vLast z : α) (uitems vitems : List (Nat × α))
    (central cut : Nat) :
    (approachWord (firstArc z vitems central) (secondArc uitems cut)).length =
      Astra3Navigation.distance (cutInput u0 vLast z uitems vitems central cut).length
        (firstEndpoint uitems) (firstEndpoint uitems + firstArc z vitems central) := by
  have cover := arcs_cover u0 vLast z uitems vitems central cut
  have lin : Astra3Navigation.linearDistance (firstEndpoint uitems)
      (firstEndpoint uitems + firstArc z vitems central) = firstArc z vitems central := by
    unfold Astra3Navigation.linearDistance
    rw [if_pos (by omega)]
    omega
  have remainder : (cutInput u0 vLast z uitems vitems central cut).length -
      firstArc z vitems central = secondArc uitems cut := by omega
  rw [approach_cost]
  unfold Astra3Navigation.distance
  rw [lin, remainder]

theorem second_endpoints_bounded (u0 vLast z : α) (uitems vitems : List (Nat × α))
    (central cut : Nat) :
    firstEndpoint uitems < (cutInput u0 vLast z uitems vitems central cut).length ∧
    firstEndpoint uitems + firstArc z vitems central <
      (cutInput u0 vLast z uitems vitems central cut).length := by
  have cover := arcs_cover u0 vLast z uitems vitems central cut
  unfold secondArc at cover
  unfold firstEndpoint
  constructor <;> omega

/- This binds the paid approach to the original modular metric, not merely
   to two convenient arc-length variables. The first approach from the
   external cursor to the selected cut and averaging over cuts remain separate. -/
theorem second_approach_modular (u0 vLast z : α) (uitems vitems : List (Nat × α))
    (central cut : Nat) :
    let n := (cutInput u0 vLast z uitems vitems central cut).length
    let x := firstEndpoint uitems
    let y := x + firstArc z vitems central
    (approachWord (firstArc z vitems central) (secondArc uitems cut)).length =
      min ((x+n-y)%n) ((y+n-x)%n) := by
  dsimp only
  rw [second_approach_exact u0 vLast z uitems vitems central cut]
  have h := second_endpoints_bounded u0 vLast z uitems vitems central cut
  exact Astra3Navigation.distance_mod _ _ _ h.1 h.2

end Astra3Block

#print axioms Astra3Block.arcs_cover
#print axioms Astra3Block.second_approach_exact
#print axioms Astra3Block.second_endpoints_bounded
#print axioms Astra3Block.second_approach_modular
