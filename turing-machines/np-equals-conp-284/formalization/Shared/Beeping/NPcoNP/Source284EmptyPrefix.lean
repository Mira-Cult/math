import Shared.Beeping.NPcoNP.Source284GuardedCoverage

/-! The clock for an empty parsed prefix is exactly one, regardless of the
candidate index. This proves a concrete first-row condition sufficient for
its separate coverage obligation. It does not implement the positive-prefix
verifier, timeout guard, witness cutoff, or physical table refinement. -/

namespace Shared.Beeping.NPcoNP.Source284EmptyPrefix

open Shared.Beeping.NPcoNP.Source284Parser
open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Beeping.NPcoNP.Source284Comparison

theorem run_length_ge (scan n e : Nat) : n ≤ (run scan n e).1 := by
  induction scan using Nat.strong_induction_on generalizing n e with
  | h scan ih =>
    by_cases hs : scan % 2 = 1
    · rw [Source284Parser.run_odd scan n e hs]
      have hpos : 0 < scan := by omega
      have hlt : scan / 4 < scan := Nat.div_lt_self hpos (by decide)
      have h := ih (scan / 4) hlt (n+1) (2*e+(scan/2)%2)
      omega
    · have he : scan % 2 = 0 := by omega
      simp [Source284Parser.run_even scan n e he]

theorem empty_iff_even (i : Nat) : Source284Parser.length i = 0 ↔ i % 2 = 0 := by
  constructor
  · intro h
    by_contra he
    have ho : i % 2 = 1 := by omega
    have hr := Source284Parser.run_odd i 0 1 ho
    have hb := run_length_ge (i/4) 1 (2+(i/2)%2)
    have hh : (Source284Parser.run (i/4) 1 (2+(i/2)%2)).1 = 0 := by
      simpa [Source284Parser.length, parse, hr] using h
    omega
  · intro h
    simp [Source284Parser.length, even_input i h]

theorem reference_empty (i : Nat) (h : Source284Parser.length i = 0) :
    reference i = false := by
  simp [reference, h]

/-- If the zero-read row has an accepting next state, every empty-prefix
input is accepted on its only available source step. -/
theorem empty_first_row (description : Nat) (hr : record description 0 < 4)
    (i : Nat) (h : Source284Parser.length i = 0) :
    acceptBound description i 1 2 = !reference i := by
  have he : i % 2 = 0 := (empty_iff_even i).1 h
  have ha : accepts description i 0 1 = true := by
    simp only [accepts_iff, Source284Relative.run_succ, Source284Relative.run_zero,
      Source284Relative.initial, Source284Relative.step]
    simp only [ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte, Nat.reduceSub, he,
      Nat.add_zero]
    have hdiv : record description 0 / 4 = 0 := Nat.div_eq_of_lt hr
    split <;> simp [hdiv]
  have hb : acceptBound description i 1 2 = true :=
    (acceptBound_iff _ _ _ _).2 ⟨0, by decide, ha⟩
  simp [hb, reference_empty i h]

end Shared.Beeping.NPcoNP.Source284EmptyPrefix
