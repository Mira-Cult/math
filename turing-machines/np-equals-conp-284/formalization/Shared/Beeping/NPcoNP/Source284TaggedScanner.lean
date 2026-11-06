import Shared.Beeping.NPcoNP.Source284TagValidator

/-! Finite composition of the two-bit tag gate with the source marker
scanner. The two tag tests and initial turn cost three transitions. Scanner
states 1–3 have exactly the original scanner's transitions; state 6 is a
continuing nonaccepting invalid-tag sink. Seven logical states are not seven
physical beeper states. This segment does not count a cutoff, truncate a
certificate, restore tape position, or enforce a witness budget. -/

namespace Shared.Beeping.NPcoNP.Source284TaggedScanner

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284WitnessScanner (lowbit_value bit_decide_mod)

/-- Logical 0 turns onto the certificate; 4 and 5 check the two tag bits;
1–3 implement the marker scanner; 6 is a permanent nonaccepting sink. -/
def table : Nat → Bool → Row
  | 0, b => ⟨b, true, some 4⟩
  | 1, b => ⟨b, false, some (if b then 2 else 3)⟩
  | 2, b => ⟨b, false, some 1⟩
  | 3, b => ⟨b, false, some 3⟩
  | 4, b => ⟨b, false, some (if b then 6 else 5)⟩
  | 5, b => ⟨b, false, some (if b then 6 else 1)⟩
  | _, b => ⟨b, false, some 6⟩

def description (tail : Nat) : Nat := encode 7 table tail

theorem table_closed : Closed 7 table := by
  intro q hq b q' hn
  interval_cases q <;> cases b <;> simp_all [table] <;> omega

theorem initial_turn (c i : Nat) :
    step table ⟨c, i, some 0⟩ = ⟨i, c, some 4⟩ := by
  simp only [step, table, ↓reduceIte]
  rw [lowbit_value]
  congr 1 <;> omega

theorem tag_step (q left right : Nat) (hq : 1 ≤ q) :
    step table ⟨left, right, some q⟩ =
      ⟨2*left + right % 2, right / 2, (table q (right.testBit 0)).next⟩ := by
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
        | succ q =>
          cases q with
          | zero => simp [step, table, bit_decide_mod]
          | succ q =>
            cases q with
            | zero => simp [step, table, bit_decide_mod]
            | succ q => simp [step, table, bit_decide_mod]

theorem run_three (c i : Nat) :
    run table ⟨c, i, some 0⟩ 3 =
      ⟨4*i + 2*(c%2) + (c/2)%2, c/4,
        some (if c%4 = 0 then 1 else 6)⟩ := by
  change step table (step table (step table ⟨c, i, some 0⟩)) = _
  rw [initial_turn, tag_step 4 i c (by omega)]
  simp only [table, Nat.testBit_zero]
  by_cases h0 : c%2 = 1
  · simp only [h0, decide_true, ↓reduceIte]
    rw [tag_step 6 _ _ (by omega)]
    simp only [table]
    have h4 : c%4 ≠ 0 := by omega
    simp only [h4, ↓reduceIte]
    congr 1 <;> omega
  · have hz : c%2 = 0 := by omega
    simp only [h0, decide_true, decide_false, Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [tag_step 5 _ _ (by omega)]
    simp only [table, Nat.testBit_zero]
    by_cases h1 : (c/2)%2 = 1
    · have h4 : c%4 ≠ 0 := by omega
      simp only [h1, h4, ↓reduceIte]
      congr 1 <;> omega
    · have h4 : c%4 = 0 := by omega
      simp only [h1, h4, ↓reduceIte]
      congr 1 <;> omega

theorem source_run (tail : Nat) (c : Config) (valid : Valid 7 c) (k : Nat) :
    Source284Relative.run (description tail) (toSource c) k = toSource (run table c k) :=
  run_toSource 7 table tail c table_closed valid k

theorem source_run_three (c i tail : Nat) :
    Source284Relative.run (description tail) (Source284Relative.initial i c) 3 =
      ⟨4*i + 2*(c%2) + (c/2)%2, c/4,
        active (if c%4 = 0 then 1 else 6)⟩ := by
  have hv : Valid 7 ⟨c, i, some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    omega
  have h := source_run tail ⟨c, i, some 0⟩ hv 3
  change Source284Relative.run (description tail) (Source284Relative.initial i c) 3 = _ at h
  rw [h, run_three]
  rfl

/-- Once invalid, the sink remains nonaccepting for every finite duration. -/
theorem sink_run (l r k : Nat) :
    (run table ⟨l, r, some 6⟩ k).state = some 6 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (step table (run table ⟨l, r, some 6⟩ k)).state = some 6
    cases hr : run table ⟨l, r, some 6⟩ k with
    | mk l' r' q =>
      simp only [hr] at ih
      subst q
      simp [step, table]

end Shared.Beeping.NPcoNP.Source284TaggedScanner
