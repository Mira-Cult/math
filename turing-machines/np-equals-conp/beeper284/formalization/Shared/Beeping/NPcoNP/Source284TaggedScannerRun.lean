import Shared.Beeping.NPcoNP.Source284TaggedScanner

/-! Run-level composition of the paid tag gate and unchanged marker scanner.
The scanner correspondence holds on actual, untruncated numeric certificates.
It does not implement a dynamic cutoff counter or reject-on-timeout wrapper. -/
namespace Shared.Beeping.NPcoNP.Source284TaggedScanner

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun

abbrev scanner := Shared.Beeping.NPcoNP.Source284WitnessScanner.table

def ScannerState (c : Config) : Prop :=
  c.state = some 1 ∨ c.state = some 2 ∨ c.state = some 3

theorem scanner_step_stays (c : Config) (h : ScannerState c) :
    ScannerState (step scanner c) := by
  rcases c with ⟨l,r,s⟩
  change s = some 1 ∨ s = some 2 ∨ s = some 3 at h
  rcases h with h | h | h <;> subst s <;> cases hb : r.testBit 0 <;>
    simp [ScannerState, step, scanner, Shared.Beeping.NPcoNP.Source284WitnessScanner.table, hb]

theorem combined_step_eq (c : Config) (h : ScannerState c) :
    step table c = step scanner c := by
  rcases c with ⟨l,r,s⟩
  change s = some 1 ∨ s = some 2 ∨ s = some 3 at h
  rcases h with h | h | h <;> subst s <;>
    simp [step, table, scanner, Shared.Beeping.NPcoNP.Source284WitnessScanner.table]

theorem scanner_run_stays (c : Config) (h : ScannerState c) (k : Nat) :
    ScannerState (run scanner c k) := by
  induction k with
  | zero => exact h
  | succ k ih => exact scanner_step_stays _ ih

theorem run_scanner_eq (c : Config) (h : ScannerState c) (k : Nat) :
    run table c k = run scanner c k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change step table (run table c k) = step scanner (run scanner c k)
    rw [ih]
    exact combined_step_eq _ (scanner_run_stays c h k)

theorem run_add (tbl : Nat → Bool → Row) (c : Config) (m n : Nat) :
    run tbl c (m+n) = run tbl (run tbl c m) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step tbl (run tbl c (m+n)) = step tbl (run tbl (run tbl c m) n)
    rw [ih]

/-- From the actual candidate start, a valid tag reaches exactly the same
logical configuration as the original scanner at one extra scanner step. -/
theorem valid_run_eq (c i k : Nat) (h : c % 4 = 0) :
    run table ⟨c,i,some 0⟩ (3+k) = run scanner ⟨c/4,4*i,some 0⟩ (1+k) := by
  have h0 : c%2 = 0 := by omega
  have h1 : (c/2)%2 = 0 := by omega
  rw [run_add, run_three]
  simp only [h, h0, h1, ↓reduceIte, Nat.mul_zero, Nat.add_zero]
  rw [run_scanner_eq _ (by simp [ScannerState])]
  rw [run_add]
  change run scanner ⟨4*i,c/4,some 1⟩ k =
    run scanner (step scanner ⟨c/4,4*i,some 0⟩) k
  rw [Shared.Beeping.NPcoNP.Source284WitnessScanner.initial_turn]

/-- Numeric source state equality, including the separately encoded scanner. -/
theorem source_valid_state (c i k tail scanTail : Nat) (h : c%4 = 0) :
    (Source284Relative.run (description tail) (Source284Relative.initial i c) (3+k)).state =
    (Source284Relative.run (Shared.Beeping.NPcoNP.Source284TableEncode.encode 4 scanner scanTail)
      (Source284Relative.initial (4*i) (c/4)) (1+k)).state := by
  have hv : Valid 7 ⟨c,i,some 0⟩ := by
    intro q hq; simp only [Option.some.injEq] at hq; omega
  have a := source_run tail ⟨c,i,some 0⟩ hv (3+k)
  change Source284Relative.run (description tail) (Source284Relative.initial i c) (3+k) = _ at a
  rw [a, Shared.Beeping.NPcoNP.Source284WitnessScanner.source_run]
  rw [valid_run_eq c i k h]

theorem source_invalid_state (c i k tail : Nat) (h : c%4 ≠ 0) :
    (Source284Relative.run (description tail) (Source284Relative.initial i c) (3+k)).state = active 6 := by
  have hv : Valid 7 ⟨c,i,some 0⟩ := by
    intro q hq; simp only [Option.some.injEq] at hq; omega
  rw [show Source284Relative.initial i c = toSource ⟨c,i,some 0⟩ by rfl,
    source_run tail _ hv, run_add, run_three]
  simp only [h, ↓reduceIte]
  change nextState (run table ⟨_,_,some 6⟩ k).state = active 6
  rw [sink_run]
  rfl

end Shared.Beeping.NPcoNP.Source284TaggedScanner
