import Shared.Beeping.NPcoNP.Source284WitnessScanner

/-! A concrete, finite relative-source segment that validates the low two
zero bits of the tagged witness certificate. The initial tape convention is
exactly that of the source candidate: the certificate is the left half and
the input is the right half. The initial turn pays one transition and
preserves the input. Two further transitions read and preserve the low
certificate bits. Both handoff states continue executing.

This checks only the two-bit tag. It does not build the tagged frame, impose
a witness cutoff, authenticate an interleaved budget, restore the head, or
prove a complexity bound. These five logical states are not physical beeper
states. -/

namespace Shared.Beeping.NPcoNP.Source284TagValidator

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284WitnessScanner (lowbit_value bit_decide_mod)

/-- The initial turn is followed by two tag-bit checks. State 3 is the
invalid-tag handoff and state 4 the valid-tag handoff. -/
def table : Nat → Bool → Row
  | 0, b => ⟨b, true, some 1⟩
  | 1, b => ⟨b, false, some (if b then 3 else 2)⟩
  | 2, b => ⟨b, false, some (if b then 3 else 4)⟩
  | 3, b => ⟨b, false, some 3⟩
  | _, b => ⟨b, false, some 4⟩

def description (tail : Nat) : Nat := encode 5 table tail

theorem table_closed : Closed 5 table := by
  intro q hq b q' hn
  interval_cases q <;> cases b <;> simp_all [table] <;> omega

theorem initial_turn (c i : Nat) :
    step table ⟨c, i, some 0⟩ = ⟨i, c, some 1⟩ := by
  simp only [step, table, ↓reduceIte]
  rw [lowbit_value]
  congr 1 <;> omega

theorem scan_step (q left right : Nat) (hq : 1 ≤ q) :
    step table ⟨left, right, some q⟩ =
      ⟨2 * left + right % 2, right / 2, (table q (right.testBit 0)).next⟩ := by
  cases q with
  | zero => omega
  | succ q =>
    cases q with
    | zero => simp [step, table, bit_decide_mod]
    | succ q =>
      cases q with
      | zero => simp [step, table, bit_decide_mod]
      | succ q =>
        cases q with
        | zero => simp [step, table, bit_decide_mod]
        | succ q => simp [step, table, bit_decide_mod]

/-- The paid three-step segment preserves the original input and all
certificate bits in its two halves, while recording tag validity in control.
The first two certificate bits are appended in scan order to the left half. -/
theorem run_three (c i : Nat) :
    run table ⟨c, i, some 0⟩ 3 =
      ⟨4 * i + 2 * (c % 2) + (c / 2) % 2, c / 4,
        some (if c % 4 = 0 then 4 else 3)⟩ := by
  change step table (step table (step table ⟨c, i, some 0⟩)) = _
  rw [initial_turn, scan_step 1 i c (by omega)]
  simp only [table, Nat.testBit_zero]
  by_cases h0 : c % 2 = 1
  · simp only [h0, decide_true, ↓reduceIte]
    rw [scan_step 3 _ _ (by omega)]
    simp only [table]
    have h4 : c % 4 ≠ 0 := by omega
    simp only [h4, ↓reduceIte]
    congr 1 <;> omega
  · have hz : c % 2 = 0 := by omega
    simp only [h0, decide_true, decide_false, Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [scan_step 2 _ _ (by omega)]
    simp only [table, Nat.testBit_zero]
    by_cases h1 : (c / 2) % 2 = 1
    · have h4 : c % 4 ≠ 0 := by omega
      simp only [h1, h4, ↓reduceIte]
      congr 1 <;> omega
    · have h4 : c % 4 = 0 := by omega
      simp only [h1, h4, ↓reduceIte]
      congr 1 <;> omega

/-- The numeric source description executes this finite table exactly;
its tail is arbitrary and the handoff is a positive active source state. -/
theorem source_run_three (c i tail : Nat) :
    Source284Relative.run (description tail) (Source284Relative.initial i c) 3 =
      ⟨4 * i + 2 * (c % 2) + (c / 2) % 2, c / 4,
       active (if c % 4 = 0 then 4 else 3)⟩ := by
  have hv : Valid 5 ⟨c, i, some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    omega
  have h := run_toSource 5 table tail ⟨c, i, some 0⟩ table_closed hv 3
  change Source284Relative.run (description tail) (Source284Relative.initial i c) 3 = _ at h
  rw [h, run_three]
  rfl

end Shared.Beeping.NPcoNP.Source284TagValidator
