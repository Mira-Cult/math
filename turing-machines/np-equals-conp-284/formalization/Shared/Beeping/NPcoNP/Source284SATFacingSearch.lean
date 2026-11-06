import Shared.Beeping.NPcoNP.Source284SATLinkedSearch
import Shared.Beeping.NPcoNP.Source284FacingAdapter

/-! SAT search through a single source table from the ordinary blank-input
orientation. Uniform polynomial construction, the source reference framing,
and literal 284-state beeper refinement are not established here. -/
namespace Shared.Beeping.NPcoNP.Source284SATFacingSearch

open Shared.Codes.FinitePrograms
open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Beeping.NPcoNP.Source284TableEncode (encode)
open Shared.Beeping.NPcoNP.Source284TableRun (run)
open Shared.Beeping.NPcoNP.Source284PairPrefixLoader (pairPrefix prefix_length)
open Shared.Beeping.NPcoNP.Source284SATGrammarCharacterization (validWindow)
open Shared.Beeping.NPcoNP.Source284SATLinkedSearch
open Shared.ComplexityBridge.BoundedHardness

/-- Add the paid initial turn to the validator and fixed verifier. -/
def description (program : Program) (x : List Bool) (width codeTail : Nat) : Nat :=
  let clock := width - (pairPrefix x).length
  let rows := Source284FiniteRelativeRows.rows program
  let validator := Source284VerifierHandoff.table (pairPrefix x) clock (Source284ListTables.table rows)
  encode (Source284CertificateDispatch.allocated (pairPrefix x) clock + rows.length + 1)
    (Source284FacingAdapter.table validator) codeTail

/-- The additional state restores the standard input/certificate convention
and adds exactly one transition to the linked source execution. -/
theorem facing_agrees (program : Program) (hv : valid program = true)
    (x : List Bool) (width certificate fuel codeTail : Nat)
    (hwidth : (pairPrefix x).length ≤ width) :
    accepts (description program x width codeTail) 0 certificate
      (((2*width+2)+(fuel+1))+1) =
      ((Source284Relative.run (Source284SATLinkedSearch.description program x width codeTail)
        (Source284TableRun.toSource ⟨0,certificate,some 0⟩)
        ((2*width+2)+(fuel+1))).state == 0) := by
  let clock := width - (pairPrefix x).length
  let rows := Source284FiniteRelativeRows.rows program
  let verifier := Source284ListTables.table rows
  let validator := Source284VerifierHandoff.table (pairPrefix x) clock verifier
  let n := Source284CertificateDispatch.allocated (pairPrefix x) clock + rows.length
  have hr : 0 < rows.length := by dsimp [rows]; simp [Source284FiniteRelativeRows.rows_length]
  have hn : 0 < n := by dsimp [n]; omega
  have hc : Source284TableRun.Closed n validator := by
    exact Source284VerifierHandoff.closed (pairPrefix x) clock rows.length verifier
      (by dsimp [rows]; simp [Source284FiniteRelativeRows.rows_length])
      (Source284FiniteRelativeRows.closed program hv)
  have h := Source284FacingAdapter.source_acceptance validator n hn hc certificate
    ((2*width+2)+(fuel+1)) codeTail
  change accepts (description program x width codeTail) 0 certificate
    (((2*width+2)+(fuel+1))+1) = _ at h
  rw [h]
  have hh := Source284VerifierReject.combined_acceptance x width certificate fuel verifier hwidth
  dsimp only at hh
  simp only [List.length_drop, Source284CanonicalPairWindow.window_length] at hh
  rw [hh]
  rw [← verifier_agrees program hv certificate (fuel+1)]
  symm
  exact Source284SATLinkedSearch.linked_acceptance program hv x width certificate fuel codeTail hwidth

/-- The SAT search now starts from the ordinary blank-input source convention.
No claim about the complexity of constructing `description` is made. -/
theorem sat_iff_facing_search :
    ∃ (program : Program) (clock : Polynomial Nat), valid program = true ∧
      ∀ (x : List Bool) (width outer codeTail : Nat),
        9*x.length+1 ≤ width → commonFuel Polynomial.X clock x+1 ≤ width →
        width ≤ outer →
        ((∃ certificate, certificate < 2^outer ∧
          accepts (description program x width codeTail) 0 certificate
            (((2*width+2)+(commonFuel Polynomial.X clock x+1))+1) = true) ↔
          Shared.ComplexityBridge.CNF.sat x = true) := by
  obtain ⟨program,clock,hvalid,hsearch⟩ := sat_iff_linked_search
  refine ⟨program,clock,hvalid,?_⟩
  intro x width outer codeTail hwidth hfuel houter
  have hpref : (pairPrefix x).length ≤ width := by
    rw [prefix_length]
    omega
  constructor
  · rintro ⟨certificate,hbound,haccept⟩
    apply (hsearch x width outer codeTail hwidth hfuel houter).1
    refine ⟨certificate,hbound,?_⟩
    rw [← facing_agrees program hvalid x width certificate
      (commonFuel Polynomial.X clock x) codeTail hpref]
    exact haccept
  · intro hsat
    obtain ⟨certificate,hbound,haccept⟩ :=
      (hsearch x width outer codeTail hwidth hfuel houter).2 hsat
    refine ⟨certificate,hbound,?_⟩
    rw [facing_agrees program hvalid x width certificate
      (commonFuel Polynomial.X clock x) codeTail hpref]
    exact haccept

end Shared.Beeping.NPcoNP.Source284SATFacingSearch
