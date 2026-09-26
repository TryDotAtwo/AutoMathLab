import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Local coordinate core for Uskov19 §4; NOT a proof of the service theorem.
M = n-1 > 0. Integer division is Euclidean (floor for positive M).
No hypotheses about existence/reachability/termination of a service are hidden here. -/
namespace LRX.UpperAffineBuffer

def passive (M H y : Int) : Int := y + 1 + (y-H)/M

def buffer (M H y : Int) : Int := H + (M+1)*((y-H)/M)

theorem buffer_forward (M H y : Int) :
    buffer M (H+1) (y+1) = buffer M H y + 1 := by
  unfold buffer
  have h : y+1-(H+1)=y-H := by ring
  rw [h]
  ring

theorem buffer_backward (M H y : Int) :
    buffer M (H-1) (y-1) = buffer M H y - 1 := by
  unfold buffer
  have h : y-1-(H-1)=y-H := by ring
  rw [h]
  ring

theorem head_positions (M H y : Int) (hhead : (y-H)%M=0) :
    passive M H y = buffer M H y + 1 := by
  have h := Int.emod_add_mul_ediv (y-H) M
  rw [hhead] at h
  unfold passive buffer
  nlinarith

theorem div_sub_one (M z : Int) (hM : 0<M) :
    (z-1)/M = z/M - if z%M=0 then 1 else 0 := by
  have he := Int.emod_add_mul_ediv z M
  have hr := Int.emod_nonneg z (by omega : M≠0)
  have hu := Int.emod_lt_of_pos z hM
  have he' := Int.emod_add_mul_ediv (z-1) M
  have hr' := Int.emod_nonneg (z-1) (by omega : M≠0)
  have hu' := Int.emod_lt_of_pos (z-1) hM
  split_ifs with hz
  · have : (z-1)/M = z/M-1 := by
      by_contra hn
      have hcases : (z-1)/M ≤ z/M-2 ∨ z/M ≤ (z-1)/M := by omega
      rcases hcases with hl|hh
      · nlinarith
      · nlinarith
    exact this
  · have : (z-1)/M = z/M := by
      by_contra hn
      have hcases : (z-1)/M ≤ z/M-1 ∨ z/M+1 ≤ (z-1)/M := by omega
      rcases hcases with hl|hh
      · have : 1 ≤ z%M := by omega
        nlinarith
      · nlinarith
    simpa using this

theorem passive_forward (M H y : Int) (hM : 0<M) :
    passive M (H+1) y = passive M H y - if (y-H)%M=0 then 1 else 0 := by
  unfold passive
  have h : y-(H+1)=(y-H)-1 := by ring
  rw [h, div_sub_one M (y-H) hM]
  ring

theorem passive_backward (M H y : Int) (hM : 0<M) :
    passive M (H-1) y = passive M H y + if (y-(H-1))%M=0 then 1 else 0 := by
  have h := passive_forward M (H-1) y hM
  have hh : H-1+1=H := by ring
  rw [hh] at h
  omega

#print axioms passive_backward
#print axioms buffer_forward
#print axioms buffer_backward
#print axioms head_positions
#print axioms div_sub_one
#print axioms passive_forward
end LRX.UpperAffineBuffer
