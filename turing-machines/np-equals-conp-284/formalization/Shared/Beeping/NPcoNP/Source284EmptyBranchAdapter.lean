import Shared.Beeping.NPcoNP.Source284HardwireTable
import Shared.Beeping.NPcoNP.Source284EmptyPrefix

/-! A paid source-table adapter for the exceptional one-step zero-prefix
case. It does not provide a timeout guard or implement any verifier. -/
namespace Shared.Beeping.NPcoNP.Source284EmptyBranchAdapter

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig run_front bit_read)

/-- Two added logical states. State zero accepts on a zero read and turns
on a one read; state one turns back while preserving the scanned symbol.
Original states are relocated by two. -/
def table (original : Nat → Bool → Row) (q : Nat) (read : Bool) : Row :=
  if q = 0 then
    if read then ⟨true,true,some 1⟩ else ⟨false,false,none⟩
  else if q = 1 then ⟨read,true,some 2⟩
  else shiftRow 2 (original (q-2) read)

theorem relocated_row (original : Nat → Bool → Row) (q : Nat) (read : Bool) :
    table original (2+q) read = shiftRow 2 (original q read) := by
  have h : 2+q ≠ 1 := by omega
  simp [table,h]

theorem relocated_step (original : Nat → Bool → Row) (c : Config) :
    step (table original) (shiftConfig 2 c) = shiftConfig 2 (step original c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (original : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table original) (shiftConfig 2 c) fuel = shiftConfig 2 (run original c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

/-- On an odd input, the paid two-step turn restores both unbounded tape
halves exactly before the original verifier starts. -/
theorem odd_initial_steps (original : Nat → Bool → Row) (input certificate : Nat)
    (hodd : input % 2 = 1) :
    run (table original) ⟨certificate,input,some 0⟩ 2 =
      shiftConfig 2 ⟨certificate,input,some 0⟩ := by
  have hb : input.testBit 0 = true := by simpa [Nat.testBit_zero] using hodd
  have hi : 2*(input/2)+1 = input := by omega
  have hc : 2*(certificate/2)+bit (certificate.testBit 0) = certificate := by
    rw [bit_read]
    omega
  have hc' : 2*(certificate/2)+(if certificate % 2 = 1 then 1 else 0) = certificate := by
    simpa [Nat.testBit_zero,bit] using hc
  simp [run,step,table,shiftConfig,hb,bit,hi,hc']

theorem odd_initial_run (original : Nat → Bool → Row) (input certificate fuel : Nat)
    (hodd : input % 2 = 1) :
    run (table original) ⟨certificate,input,some 0⟩ (fuel+2) =
      shiftConfig 2 (run original ⟨certificate,input,some 0⟩ fuel) := by
  have hs : step (table original) (step (table original) ⟨certificate,input,some 0⟩) =
      shiftConfig 2 ⟨certificate,input,some 0⟩ := by
    simpa [run] using odd_initial_steps original input certificate hodd
  rw [show fuel+2 = (fuel+1)+1 by omega,run_front,run_front,hs,relocated_run]

/-- The two added logical states preserve finite-state closure. -/
theorem closed (original : Nat → Bool → Row) (n : Nat)
    (hn : 0 < n) (hclosed : Closed n original) : Closed (n+2) (table original) := by
  intro q hq read q' hnext
  by_cases hz : q = 0
  · subst q
    cases read <;> simp [table] at hnext <;> omega
  · by_cases ho : q = 1
    · subst q
      simp [table] at hnext
      omega
    · have hq' : q-2 < n := by omega
      simp only [table,if_neg hz,if_neg ho,shiftRow] at hnext
      cases hr : (original (q-2) read).next with
      | none => simp [hr] at hnext
      | some r =>
          have hh := hclosed (q-2) hq' read r hr
          simp only [hr,Option.map_some,Option.some.injEq] at hnext
          omega

/-- The first encoded row is an immediate accepting transition. -/
theorem encoded_first_record (original : Nat → Bool → Row) (n tail : Nat) :
    Source284Relative.record (encode (n+2) (table original) tail) 0 = 0 := by
  have h := record_lookup (n+2) (table original) tail 0 (by omega) false
  simpa [active,bit,table,rowCode,nextState] using h

/-- The adapter's finite table contains exactly two rows per logical state.
The source's active-state encoding uses odd positive numbers. -/
theorem encoding_cost (original : Nat → Bool → Row) (n : Nat) :
    (records (n+2) (table original)).length = 2*(n+2) ∧
      active (n+1) = 2*n+3 := by
  simp [records,active]
  omega

/-- Every individual certificate accepts the zero-prefix case at its first
source iteration, including all values of the ignored input suffix. -/
theorem encoded_empty_attempt (original : Nat → Bool → Row) (n tail input certificate : Nat)
    (hzero : Source284Parser.length input = 0) :
    Source284Relative.accepts (encode (n+2) (table original) tail) input certificate 1 = true := by
  have he := (Source284EmptyPrefix.empty_iff_even input).1 hzero
  simp [Source284Relative.accepts,Source284Relative.run,Source284Relative.initial,
    Source284Relative.step,he,encoded_first_record]

/-- Every zero-prefix source input is accepted within its actual one-step
clock, independently of the certificate or ignored high suffix. -/
theorem encoded_empty (original : Nat → Bool → Row) (n tail input : Nat)
    (hzero : Source284Parser.length input = 0) :
    Source284Relative.acceptBound (encode (n+2) (table original) tail) input 1 2 =
      !Source284Comparison.reference input := by
  apply Source284EmptyPrefix.empty_first_row
  · rw [encoded_first_record]
    decide
  · exact hzero

/-- After its two paid setup steps, the encoded adapter has exactly the
original table's acceptance behavior on every odd input and certificate. -/
theorem encoded_odd_acceptance (original : Nat → Bool → Row) (n tail input certificate fuel : Nat)
    (hn : 0 < n) (hclosed : Closed n original) (hodd : input % 2 = 1) :
    Source284Relative.accepts (encode (n+2) (table original) tail) input certificate (fuel+2) =
      Source284Relative.accepts (encode n original 0) input certificate fuel := by
  rw [bounded_acceptance (n+2) (table original) tail (by omega) (closed original n hn hclosed),
    odd_initial_run original input certificate fuel hodd,
    bounded_acceptance n original 0 hn hclosed]
  change ((run original ⟨certificate,input,some 0⟩ fuel).state.map (fun q => 2+q)).isNone = _
  cases h : (run original ⟨certificate,input,some 0⟩ fuel).state <;> simp [h]

/-- The same two-step overhead preserves the complete bounded existential
certificate search, not just an individual attempt. -/
theorem encoded_odd_search (original : Nat → Bool → Row) (n tail input fuel bound : Nat)
    (hn : 0 < n) (hclosed : Closed n original) (hodd : input % 2 = 1) :
    Source284Relative.acceptBound (encode (n+2) (table original) tail) input (fuel+2) bound =
      Source284Relative.acceptBound (encode n original 0) input fuel bound := by
  simp only [Source284Relative.acceptBound,encoded_odd_acceptance original n tail input _ fuel hn hclosed hodd]

end Shared.Beeping.NPcoNP.Source284EmptyBranchAdapter
