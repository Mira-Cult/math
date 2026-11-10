import Mathlib.Tactic.Linarith

/-!
The exact Cantor orientation of the pinned PA producer. This is not mathlib's different square-pairing enumeration.
`unpairAux` is the source's subtractive loop with a kernel-checked decreasing
natural measure. Its correctness and fairness do not assume theory soundness.
-/
namespace PASoundness.Cantor

def triangle : Nat → Nat
  | 0 => 0
  | n + 1 => triangle n + (n + 1)

theorem triangle_twice (n : Nat) : 2 * triangle n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [triangle]; nlinarith

theorem triangle_closed (n : Nat) : triangle n = n * (n + 1) / 2 := by
  have h : n * (n + 1) = triangle n * 2 := by nlinarith [triangle_twice n]
  simp [h]

theorem triangle_mono {m n : Nat} (h : m ≤ n) : triangle m ≤ triangle n := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step n h ih => simp only [triangle]; omega

theorem triangle_ge (n : Nat) : n ≤ triangle n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih => simp only [triangle]; omega

/-- `b` is the low coordinate, exactly as in compact/source.py. -/
def pair (a b : Nat) : Nat := triangle (a + b) + b

theorem pair_eq_source (a b : Nat) :
    pair a b = (a + b) * (a + b + 1) / 2 + b := by
  rw [pair, triangle_closed]

def fastPair (a b : Nat) : Nat := (a+b) * (a+b+1) / 2 + b

/-- Native evaluation uses the producer's closed arithmetic expression. The
compiler rewrite is itself a kernel-checked function equality. -/
@[csimp] theorem pair_compiled : @pair = @fastPair := by
  funext a b
  exact pair_eq_source a b

theorem pair_bounds (a b : Nat) :
    triangle (a+b) ≤ pair a b ∧ pair a b < triangle (a+b+1) := by
  simp only [pair, triangle]
  omega

theorem pair_injective {a b c d : Nat} (h : pair a b = pair c d) : a = c ∧ b = d := by
  have hab := pair_bounds a b
  have hcd := pair_bounds c d
  have hs : a+b = c+d := by
    by_contra hn
    cases Nat.lt_or_gt_of_ne hn with
    | inl hl =>
      have hm := triangle_mono (Nat.succ_le_of_lt hl)
      simp only [Nat.succ_eq_add_one] at hm
      omega
    | inr hl =>
      have hm := triangle_mono (Nat.succ_le_of_lt hl)
      simp only [Nat.succ_eq_add_one] at hm
      omega
  simp only [pair, hs] at h
  constructor <;> omega

theorem left_le_pair (a b : Nat) : a ≤ pair a b := by
  have hg := triangle_ge (a+b)
  simp only [pair]
  omega

theorem right_le_pair (a b : Nat) : b ≤ pair a b := by
  simp only [pair]
  omega

/-- The finite subtractive inverse loop, matching w+=1; z-=w. -/
def unpairAux (w z : Nat) : Nat × Nat :=
  if z ≤ w then (w-z, z) else unpairAux (w+1) (z-(w+1))
termination_by z
decreasing_by omega

theorem unpairAux_correct (w z : Nat) :
    pair (unpairAux w z).1 (unpairAux w z).2 = triangle w + z := by
  induction z using Nat.strong_induction_on generalizing w with
  | h z ih =>
    rw [unpairAux]
    split
    next h => simp only [pair, Nat.sub_add_cancel h]
    next h =>
      have hz : z-(w+1) < z := by omega
      rw [ih _ hz (w+1), triangle]
      omega

def unpair (z : Nat) : Nat × Nat := unpairAux 0 z

@[simp] theorem pair_unpair (z : Nat) : pair (unpair z).1 (unpair z).2 = z := by
  simpa [unpair, triangle] using unpairAux_correct 0 z

@[simp] theorem unpair_pair (a b : Nat) : unpair (pair a b) = (a,b) := by
  obtain ⟨h₁, h₂⟩ := pair_injective (pair_unpair (pair a b))
  exact Prod.ext h₁ h₂

theorem unpair_fst_le (z : Nat) : (unpair z).1 ≤ z := by
  simpa using left_le_pair (unpair z).1 (unpair z).2

theorem unpair_snd_le (z : Nat) : (unpair z).2 ≤ z := by
  simpa using right_le_pair (unpair z).1 (unpair z).2


end PASoundness.Cantor
