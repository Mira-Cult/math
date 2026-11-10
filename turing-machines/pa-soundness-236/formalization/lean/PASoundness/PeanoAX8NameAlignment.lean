import PASoundness.PeanoAX8ParkNames
import PASoundness.PeanoAX8InstallNames
import PASoundness.PeanoFreeNameVacate
import PASoundness.PeanoFreeNameVacateLow
import PASoundness.PeanoFreeNamePermutationInverse

/-! A finite-swap action for freshening the non-alias AX8 variable layout.
Formula alignment and an AX8 derivation remain separate obligations. -/
namespace PASoundness.PeanoAX8NameAlignment
open PeanoFreeNamePermutation PeanoFreeNamePermutationInverse
open PeanoAX8ParkNames PeanoAX8InstallNames PeanoFreeNameVacate

/-- Park the three distinguished names, vacate the low block, then install
the distinguished names at the fixed canonical positions. -/
def alignment (a b c base : Nat) : List (Nat × Nat) :=
  (park a b c base ++ vacate (base+3)) ++ install base

private theorem vacate_parked (base r : Nat) (hb : 6 < base) (hr : r ≤ 2) :
    applyName (vacate (base+3)) (base+r) = base+r := by
  apply outside_action
  · omega
  · omega
  · left; omega

theorem alignment_a (a b c base : Nat) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (ha : a < base) (hb : b < base) (hc : c < base) (hs : 6 < base) :
    applyName (alignment a b c base) a = 4 := by
  rw [alignment, applyName_append, applyName_append,
    park_a a b c base hab hac hbc ha hb hc]
  simpa only [Nat.add_zero] using congrArg (applyName (install base))
    (vacate_parked base 0 hs (by omega)) |>.trans (install_first base hs)

theorem alignment_b (a b c base : Nat) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (ha : a < base) (hb : b < base) (hc : c < base) (hs : 6 < base) :
    applyName (alignment a b c base) b = 5 := by
  rw [alignment, applyName_append, applyName_append,
    park_b a b c base hab hac hbc ha hb hc, vacate_parked base 1 hs (by omega)]
  exact install_second base hs

theorem alignment_c (a b c base : Nat) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (ha : a < base) (hb : b < base) (hc : c < base) (hs : 6 < base) :
    applyName (alignment a b c base) c = 3 := by
  rw [alignment, applyName_append, applyName_append,
    park_c a b c base hab hac hbc ha hb hc, vacate_parked base 2 hs (by omega)]
  exact install_third base hs

/-- Other names below the fresh base leave the reserved low-name set. -/
theorem alignment_other (a b c base n : Nat) (_hab : a ≠ b) (_hac : a ≠ c)
    (_hbc : b ≠ c) (_ha : a < base) (_hb : b < base) (_hc : c < base) (hs : 6 < base)
    (hn : n < base) (hna : n ≠ a) (hnb : n ≠ b) (hnc : n ≠ c) :
    6 ≤ applyName (alignment a b c base) n := by
  rw [alignment, applyName_append, applyName_append, park_other a b c base n hn hna hnb hnc]
  by_cases hsmall : n < 6
  · have hv : applyName (vacate (base+3)) n = base+3+n := by
      exact PeanoFreeNameVacateLow.low_action (base+3) n (by omega) hsmall
    rw [hv, install_other base (base+3+n) hs (by omega) (by omega) (by omega) (by omega)]
    omega
  · have hv : applyName (vacate (base+3)) n = n :=
      outside_action (base+3) n (by omega) (by omega) (Or.inl (by omega))
    rw [hv, install_other base n hs (by omega) (by omega) (by omega) (by omega)]
    omega

/-- For any finite support, a concrete swap list aligns three pairwise
distinct names and moves every other supported name outside positions 0–5. -/
theorem exists_alignment (support : Finset Nat) (a b c : Nat)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ xs : List (Nat × Nat),
      applyName xs a = 4 ∧ applyName xs b = 5 ∧ applyName xs c = 3 ∧
      ∀ n ∈ support, n ≠ a → n ≠ b → n ≠ c → 6 ≤ applyName xs n := by
  let base := max (max (max a b) c) (support.sup id) + 7
  have ha : a < base := by dsimp [base]; omega
  have hb : b < base := by dsimp [base]; omega
  have hc : c < base := by dsimp [base]; omega
  have hs : 6 < base := by dsimp [base]; omega
  refine ⟨alignment a b c base, alignment_a a b c base hab hac hbc ha hb hc hs,
    alignment_b a b c base hab hac hbc ha hb hc hs,
    alignment_c a b c base hab hac hbc ha hb hc hs, ?_⟩
  intro n hn hna hnb hnc
  have hns : n ≤ support.sup id := Finset.le_sup (f := id) hn
  have hnbound : n < base := by dsimp [base]; omega
  exact alignment_other a b c base n hab hac hbc ha hb hc hs hnbound hna hnb hnc

end PASoundness.PeanoAX8NameAlignment

#print axioms PASoundness.PeanoAX8NameAlignment.exists_alignment
