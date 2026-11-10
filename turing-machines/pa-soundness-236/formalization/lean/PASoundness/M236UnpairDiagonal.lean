import PASoundness.Cantor
/-! Arithmetic invariant for the selected graph's diagonal unpairing loop. -/
namespace PASoundness.M236.UnpairDiagonal
open PASoundness.Cantor

def next : Nat × Nat → Nat × Nat
  | (0, c) => (c+1, 0)
  | (a+1, c) => (a, c+1)

theorem pair_next (a c : Nat) : pair (next (a,c)).1 (next (a,c)).2 = pair a c + 1 := by
  cases a with
  | zero => simp [next, pair, triangle]; omega
  | succ a =>
    simp only [next, pair]
    have h : a + (c+1) = (a+1) + c := by omega
    rw [h]
    omega

def walk : Nat → Nat × Nat → Nat × Nat
  | 0, p => p
  | n+1, p => walk n (next p)

theorem pair_walk (n : Nat) (p : Nat × Nat) :
    pair (walk n p).1 (walk n p).2 = pair p.1 p.2 + n := by
  induction n generalizing p with
  | zero => simp [walk]
  | succ n ih =>
    simp only [walk, ih]
    rcases p with ⟨a,c⟩
    simp only [Prod.fst, Prod.snd] at *
    rw [pair_next]
    omega

/-- Starting at `(0,0)`, any finite number of diagonal steps gives the
producer's exact Cantor inverse, with no bound on the input. -/
theorem walk_zero (n : Nat) : walk n (0,0) = unpair n := by
  have h := pair_walk n (0,0)
  have hzero : pair 0 0 = 0 := by rfl
  rw [hzero, Nat.zero_add] at h
  have hi := pair_injective (h.trans (pair_unpair n).symm)
  exact Prod.ext hi.1 hi.2
end PASoundness.M236.UnpairDiagonal
