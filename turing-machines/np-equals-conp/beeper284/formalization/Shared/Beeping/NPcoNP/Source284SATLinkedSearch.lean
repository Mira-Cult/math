import Shared.Beeping.NPcoNP.Source284VerifierLinkedSource
import Shared.Beeping.NPcoNP.Source284SATWindowSoundness
import Shared.Beeping.NPcoNP.Source284FiniteRelativeRun
import Shared.Beeping.NPcoNP.Source284ClockStability

/-! SAT characterized by a single encoded source table running a validator
and verifier. The certificate is already under the head. Constructing this
table uniformly in polynomial time, initializing its tape and proving the
literal 284-state beeper are separate obligations. -/
namespace Shared.Beeping.NPcoNP.Source284SATLinkedSearch

open Shared.Codes.FinitePrograms
open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Beeping.NPcoNP.Source284TableEncode (encode)
open Shared.Beeping.NPcoNP.Source284TableRun (run toSource bounded_acceptance)
open Shared.Beeping.NPcoNP.Source284PairPrefixLoader (pairPrefix prefix_length)
open Shared.Beeping.NPcoNP.Source284CanonicalPairWindow (window)
open Shared.Beeping.NPcoNP.Source284SATGrammarCharacterization
open Shared.Beeping.NPcoNP.Source284SATWindowSoundness
open Shared.ComplexityBridge.BoundedHardness

/-- The table depends on the public input and the window length, but not on
the certificate or the eventual SAT answer. -/
def description (program : Program) (x : List Bool) (width codeTail : Nat) : Nat :=
  let clock := width - (pairPrefix x).length
  let rows := Source284FiniteRelativeRows.rows program
  encode (Source284CertificateDispatch.allocated (pairPrefix x) clock + rows.length)
    (Source284VerifierHandoff.table (pairPrefix x) clock (Source284ListTables.table rows)) codeTail

theorem verifier_agrees (program : Program) (hv : valid program = true)
    (certificate fuel : Nat) :
    accepts (value (Source284CompileBitsTM2.compileBits program)) certificate 0 fuel =
      (run (Source284ListTables.table (Source284FiniteRelativeRows.rows program))
        ⟨0,certificate,some 0⟩ fuel).state.isNone := by
  have hn : 0 < (Source284FiniteRelativeRows.rows program).length := by
    simp [Source284FiniteRelativeRows.rows_length]
  have h := bounded_acceptance (Source284FiniteRelativeRows.rows program).length
    (Source284ListTables.table (Source284FiniteRelativeRows.rows program)) 1 hn
    (Source284FiniteRelativeRows.closed program hv) certificate 0 fuel
  rw [Source284FiniteRelativeRun.encode_eq_compile] at h
  exact (Source284CompileBitsTM2.compileBits_accepts program hv certificate 0 fuel).trans h

/-- The linked source table implements the SAT grammar filter and verifier in
one finite run. The `fuel+1` verifier clock is explicitly paid. -/
theorem linked_acceptance (program : Program) (hv : valid program = true)
    (x : List Bool) (width certificate fuel codeTail : Nat)
    (hwidth : (pairPrefix x).length ≤ width) :
    ((Source284Relative.run (description program x width codeTail)
      (toSource ⟨0,certificate,some 0⟩) ((2*width+2)+(fuel+1))).state == 0) =
      (validWindow x width certificate &&
        accepts (value (Source284CompileBitsTM2.compileBits program)) certificate 0 (fuel+1)) := by
  have h := Source284VerifierLinkedSource.source_combined_acceptance x width certificate fuel codeTail
    (Source284FiniteRelativeRows.rows program).length
    (Source284ListTables.table (Source284FiniteRelativeRows.rows program))
    (by simp [Source284FiniteRelativeRows.rows_length])
    (Source284FiniteRelativeRows.closed program hv) hwidth
  dsimp only at h
  simp only [List.length_drop, Source284CanonicalPairWindow.window_length] at h
  rw [← verifier_agrees program hv certificate (fuel+1)] at h
  simpa [description] using h

/-- SAT is equivalent to bounded certificate search through one encoded
validator/verifier table for each public input and window length. This is a
semantic characterization, not yet a polynomial-time many-one reduction. -/
theorem sat_iff_linked_search :
    ∃ (program : Program) (clock : Polynomial Nat), valid program = true ∧
      ∀ (x : List Bool) (width outer codeTail : Nat),
        9*x.length+1 ≤ width → commonFuel Polynomial.X clock x+1 ≤ width →
        width ≤ outer →
        ((∃ certificate, certificate < 2^outer ∧
          ((Source284Relative.run (description program x width codeTail)
            (toSource ⟨0,certificate,some 0⟩)
            ((2*width+2)+(commonFuel Polynomial.X clock x+1))).state == 0) = true) ↔
          Shared.ComplexityBridge.CNF.sat x = true) := by
  obtain ⟨program,clock,hvalid,hsound,hcomplete⟩ := sat_fixed_verifier_window_sound
  refine ⟨program,clock,hvalid,?_⟩
  intro x width outer codeTail hwidth hfuel houter
  have hpref : (pairPrefix x).length ≤ width := by
    rw [prefix_length]
    omega
  constructor
  · rintro ⟨certificate,_,haccept⟩
    rw [linked_acceptance program hvalid x width certificate
      (commonFuel Polynomial.X clock x) codeTail hpref] at haccept
    simp only [Bool.and_eq_true] at haccept
    obtain ⟨w,hwindow⟩ := validWindow_sound x width certificate haccept.1
    exact hsound x w _ width certificate hfuel hwindow haccept.2
  · intro hsat
    obtain ⟨w,hw,haccept⟩ := hcomplete x hsat
    let certificate := value (BitstringEncoding.bitEncode (x,w))
    have hlen : (BitstringEncoding.bitEncode (x,w)).length ≤ outer := by
      rw [Shared.ComplexityBridge.bitstring_pair_encoded_length]
      omega
    have hbound : certificate < 2^outer := by
      exact lt_of_lt_of_le
        (Source284Witness.value_lt_pow_length _)
        (Nat.pow_le_pow_right (by decide) hlen)
    have hvalidWindow : validWindow x width certificate = true :=
      validWindow_complete x w width hw hwidth
    have hmore : accepts (value (Source284CompileBitsTM2.compileBits program)) certificate 0
        (commonFuel Polynomial.X clock x+1) = true := by
      exact accepts_clock_mono _ _ _ _ 1 haccept
    refine ⟨certificate,hbound,?_⟩
    rw [linked_acceptance program hvalid x width certificate
      (commonFuel Polynomial.X clock x) codeTail hpref]
    simp [hvalidWindow,hmore]

end Shared.Beeping.NPcoNP.Source284SATLinkedSearch
