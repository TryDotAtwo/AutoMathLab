import LRX.ReducedPrice

/-! Constructive, upper-bound-only audit of the short interval-reversal word.
No shortestness or disjoint-support additivity is asserted. -/
namespace LRX.Cycle11BlockReversal
open LRX.BlockExchange LRX.ReducedPrice
variable {α : Type*}

def ends : Nat → List Op
  | 0 => [.X]
  | k+1 => [.X,.L] ++ ends k ++ [.R,.X]

theorem ends_length (k : Nat) : (ends k).length=4*k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [ends,ih]; omega

/-- Swap the two endpoints, leaving the entire intervening list unchanged. -/
theorem ends_run (t rest : List α) (a b : α) :
    run (ends t.length) (a :: (t ++ b :: rest)) = b :: (t ++ a :: rest) := by
  induction t generalizing rest a b with
  | nil => rfl
  | cons c t ih =>
    simp only [List.length_cons, ends, run_append]
    have h : run [.X,.L] (a :: ((c::t) ++ b::rest)) =
        a :: (t ++ b :: (rest ++ [c])) := by
      simp [run,step,swap,left,List.append_assoc]
    rw [h,ih]
    simp [run,step,right,left,swap,List.append_assoc]

/-- k is the number of elements being reversed. -/
def zig : Nat → List Op
  | 0 => []
  | 1 => []
  | 2 => ends 0
  | 3 => ends 1
  | k+4 => ends (k+2) ++ [.L] ++ zig (k+2)

def offset : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | k+4 => 1 + offset (k+2)

theorem offset_formula (k : Nat) (hk : 2≤k) : offset k=k/2-1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 => omega
    | 1 => omega
    | 2 => rfl
    | 3 => rfl
    | k+4 =>
      rw [offset,ih (k+2) (by omega) (by omega)]
      omega

theorem zig_length (k : Nat) (hk : 2≤k) : (zig k).length+1=k*(k-1) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 => omega
    | 1 => omega
    | 2 => rfl
    | 3 => rfl
    | k+4 =>
      have h := ih (k+2) (by omega) (by omega)
      simp only [zig,List.length_append,List.length_cons,List.length_nil,ends_length]
      have hsub : k+2-1=k+1 := by omega
      have hsub' : k+4-1=k+3 := by omega
      rw [hsub] at h
      rw [hsub']
      nlinarith

/-- A literal reversal of a contiguous block, with the cursor displacement paid
by the word itself. Outside entries need not be distinct. -/
theorem zig_run (k : Nat) (p rest : List α) (hp : p.length=k) :
    run (zig k) (p++rest) = run (spin (offset k : Int)) (p.reverse++rest) := by
  induction k using Nat.strong_induction_on generalizing p rest with
  | h k ih =>
    cases p with
    | nil => subst k; rfl
    | cons a tail =>
      cases ht : tail.reverse with
      | nil =>
        have he : tail=[] := by simpa using congrArg List.reverse ht
        subst tail
        have he : k=1 := by simpa using hp.symm
        subst k
        rfl
      | cons b revmid =>
        have he : tail=revmid.reverse++[b] := by simpa using congrArg List.reverse ht
        rw [he] at hp ⊢
        generalize hm : revmid.reverse = mid at hp ⊢
        have hk : k=mid.length+2 := by simpa [List.length_append] using hp.symm
        clear hp
        subst k
        cases mid with
        | nil => simp [zig,ends,offset,run,step,swap,spin]
        | cons x mid =>
          cases mid with
          | nil => simp [zig,ends,offset,run,step,swap,left,right,spin]
          | cons y mid =>
            have hi := ih (mid.length+2) (by simp)
              (x::y::mid) ((a::rest)++[b]) (by simp)
            have hr := ends_run (x::y::mid) rest a b
            have hs : (offset (mid.length+4) : Int) = 1+(offset (mid.length+2) : Int) := by
              simp [offset]
            simp only [List.length_cons] at *
            change run (ends (mid.length+2) ++ [.L] ++ zig (mid.length+2))
                ((a::((x::y::mid)++[b]))++rest) = _
            rw [run_append,run_append]
            have he' : ((a::((x::y::mid)++[b]))++rest) =
                a::((x::y::mid)++b::rest) := by simp
            rw [he',hr]
            have hl : run [.L] (b::((x::y::mid)++a::rest)) =
                (x::y::mid)++((a::rest)++[b]) := by simp [run,step,left,List.append_assoc]
            rw [hl,hi]
            rw [hs,spin_add]
            simp [spin,run,step,left,List.append_assoc]

def common (c f : Nat) : List Op := (zig c).reverse ++ [.L,.L] ++ zig f

theorem half_budget (f c : Nat) (hf : 2≤f) (hfc : f≤c) (hcf : c≤f+1) :
    2*(c*(c-1)+f*(f-1)+f)=(c+f)*(c+f-1) := by
  have hc : c=f ∨ c=f+1 := by omega
  have hs : f-1+1=f := by omega
  have ht : c-1+1=c := by omega
  have hu : c+f-1+1=c+f := by omega
  rcases hc with hc | hc <;> subst c <;> nlinarith

theorem common_budget (f c : Nat) (hf : 2≤f) (hfc : f≤c) (hcf : c≤f+1)
    (finish : List Op) (hfinish : finish.length≤f) :
    (common c f ++ finish).length≤(c+f)*(c+f-1)/2 := by
  have h1 := zig_length f hf
  have h2 := zig_length c (by omega)
  have h3 := half_budget f c hf hfc hcf
  simp only [common,List.length_append,List.length_reverse,List.length_cons,List.length_nil]
  omega

#print axioms ends_run
#print axioms offset_formula
#print axioms zig_length
#print axioms zig_run
#print axioms common_budget
end LRX.Cycle11BlockReversal
