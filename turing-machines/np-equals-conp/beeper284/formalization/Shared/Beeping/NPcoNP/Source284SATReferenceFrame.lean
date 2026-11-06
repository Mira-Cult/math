import Shared.Beeping.NPcoNP.Source284SATFacingSearch
import Shared.Beeping.NPcoNP.Source284MaterializeRows
import Shared.Beeping.NPcoNP.Source284GuardedFrameCorrect
import Shared.Beeping.NPcoNP.Source284SATWindowClock
import Shared.Beeping.NPcoNP.Source284CanonicalConditional

/-! Explicit finite tables and reference frames for the SAT source search.
The remaining reduction-cost obligation is polynomial-time construction of
`tableRows`; no complexity claim is made for that function here. -/
namespace Shared.Beeping.NPcoNP.Source284SATReferenceFrame

open Shared.Codes.FinitePrograms
open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284PairPrefixLoader (pairPrefix)
open Shared.Beeping.NPcoNP.Source284SATWindowClock
open Shared.Beeping.NPcoNP.Source284SATFacingSearch
open Shared.ComplexityBridge.BoundedHardness

def windowSize (clock : Polynomial Nat) (x : List Bool) : Nat :=
  (windowTokens clock 1 x).length

def cutoff (clock : Polynomial Nat) (x : List Bool) : List Bool :=
  outerTokens clock 1 x

def stateCount (program : Program) (x : List Bool) (width : Nat) : Nat :=
  Source284CertificateDispatch.allocated (pairPrefix x) (width-(pairPrefix x).length) +
    (Source284FiniteRelativeRows.rows program).length + 1

def facedTable (program : Program) (x : List Bool) (width : Nat) : Nat → Bool → Source284TableEncode.Row :=
  Source284FacingAdapter.table
    (Source284VerifierHandoff.table (pairPrefix x) (width-(pairPrefix x).length)
      (Source284ListTables.table (Source284FiniteRelativeRows.rows program)))

/-- An explicit finite row list, parameterized only by public input and fixed
verifier data. Its polynomial construction cost remains to be proved. -/
def tableRows (program : Program) (clock : Polynomial Nat) (x : List Bool) : EncRows :=
  Source284MaterializeRows.rows (stateCount program x (windowSize clock x))
    (facedTable program x (windowSize clock x))

theorem stateCount_pos (program : Program) (x : List Bool) (width : Nat) :
    0 < stateCount program x width := by simp [stateCount]

theorem faced_closed (program : Program) (hv : valid program = true)
    (x : List Bool) (width : Nat) :
    Closed (stateCount program x width) (facedTable program x width) := by
  have hn : 0 < (Source284FiniteRelativeRows.rows program).length := by
    simp [Source284FiniteRelativeRows.rows_length]
  have hc := Source284VerifierHandoff.closed (pairPrefix x) (width-(pairPrefix x).length)
    (Source284FiniteRelativeRows.rows program).length
    (Source284ListTables.table (Source284FiniteRelativeRows.rows program)) hn
    (Source284FiniteRelativeRows.closed program hv)
  apply Source284FacingAdapter.closed _ _ (by omega) hc

theorem tableRows_closed (program : Program) (hv : valid program = true)
    (clock : Polynomial Nat) (x : List Bool) :
    Closed (tableRows program clock x).length
      (Source284ListTables.table (decodeRows (tableRows program clock x))) := by
  exact Source284MaterializeRows.table_closed _ _ (faced_closed program hv x _)

theorem cutoff_length (clock : Polynomial Nat) (x : List Bool) :
    (cutoff clock x).length =
      ((2*windowSize clock x+2)+(commonFuel Polynomial.X clock x+1))+1 := by
  simp only [cutoff,outer_length,windowSize]
  omega

theorem source_eq (program : Program) (clock : Polynomial Nat) (x : List Bool) :
    encode (tableRows program clock x).length
        (Source284ListTables.table (decodeRows (tableRows program clock x))) 0 =
      Source284SATFacingSearch.description program x (windowSize clock x) 0 := by
  rw [show tableRows program clock x = Source284MaterializeRows.rows
    (stateCount program x (windowSize clock x)) (facedTable program x (windowSize clock x)) by rfl]
  rw [Source284MaterializeRows.encode_agrees]
  rfl

/-- The literal frame has the SAT truth value. This result does not claim
that `tableRows` can be constructed in polynomial time. -/
theorem sat_reference_frame :
    ∃ (program : Program) (clock : Polynomial Nat), valid program = true ∧
      ∀ x : List Bool,
        Source284Comparison.reference
          (value (Source284GuardedFrameTM2.frame ([],(cutoff clock x,tableRows program clock x)))) = true ↔
          Shared.ComplexityBridge.CNF.sat x = true := by
  obtain ⟨program,clock,hvalid,hsearch⟩ := sat_iff_facing_search
  refine ⟨program,clock,hvalid,?_⟩
  intro x
  have hn : 0 < (tableRows program clock x).length := by
    simp [tableRows,Source284MaterializeRows.rows_length,stateCount_pos]
  have hc := tableRows_closed program hvalid clock x
  rw [Source284GuardedFrameCorrect.reference_exact [] (cutoff clock x) (tableRows program clock x) hn hc]
  have ht : (cutoff clock x).length =
      ((2*windowSize clock x+2)+(commonFuel Polynomial.X clock x+1))+1 := cutoff_length clock x
  have hw : 9*x.length+1 ≤ windowSize clock x := pair_bound_le clock 1 x
  have hf : commonFuel Polynomial.X clock x+1 ≤ windowSize clock x := fuel_with_slack_le clock 1 x
  have ho : windowSize clock x ≤ (cutoff clock x).length := window_le_outer clock 1 x
  have htable (certificate : Nat) :
      (run (Source284ListTables.table (decodeRows (tableRows program clock x)))
        ⟨certificate,value [],some 0⟩ (cutoff clock x).length).state.isNone =
      Source284Relative.accepts (Source284SATFacingSearch.description program x (windowSize clock x) 0)
        0 certificate (cutoff clock x).length := by
    have h := bounded_acceptance (tableRows program clock x).length
      (Source284ListTables.table (decodeRows (tableRows program clock x))) 0 hn hc
      0 certificate (cutoff clock x).length
    rw [source_eq] at h
    simpa [value] using h.symm
  simp_rw [htable,ht]
  simpa only [ht] using hsearch x (windowSize clock x) (cutoff clock x).length 0 hw hf ho

/-- The actual all-bitstring many-one map, provided as an executable function.
It is polynomial once its input-dependent finite table rows are. -/
def reduction (program : Program) (clock : Polynomial Nat) (x : List Bool) : List Bool :=
  Source284GuardedFrameTM2.frame ([],(cutoff clock x,tableRows program clock x))

theorem reduction_isPolyTime (program : Program) (clock : Polynomial Nat)
    (hrows : ComplexityTheory.IsPolyTime (tableRows program clock)) :
    ComplexityTheory.IsPolyTime (reduction program clock) := by
  let pub : List Bool → List Bool := fun _ => []
  let ticks : List Bool → List Bool := cutoff clock
  let generated : List Bool → EncRows := tableRows program clock
  have hp : ComplexityTheory.IsPolyTime pub := Shared.ComplexityBridge.TM2EmptyConstant.isPolyTime [] rfl
  have ht : ComplexityTheory.IsPolyTime ticks := outer_isPolyTime clock 1
  have hg : ComplexityTheory.IsPolyTime generated := hrows
  have ha := Shared.ComplexityBridge.TM2GuardAllStep.pair_isPolyTime pub
    (fun x => (ticks x,generated x)) hp
    (Shared.ComplexityBridge.TM2GuardAllStep.pair_isPolyTime ticks generated ht hg)
  have hh := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp
    (fun x => (pub x,(ticks x,generated x))) Source284GuardedFrameTM2.frame ha
    Source284GuardedFrameTM2.frame_isPolyTime
  exact hh

/-- For a fixed verifier and clock satisfying the proved frame semantics,
the only additional reduction premise is polynomial-time row construction. -/
theorem sat_hard_of_rows (program : Program) (clock : Polynomial Nat)
    (hrows : ComplexityTheory.IsPolyTime (tableRows program clock))
    (hsemantic : ∀ x, Source284Comparison.reference
      (value (reduction program clock x)) = true ↔ Shared.ComplexityBridge.CNF.sat x = true) :
    Shared.ComplexityBridge.CanonicalClasses.PolyRed Shared.ComplexityBridge.CNF.sat
      Source284CanonicalConditional.referenceLanguage := by
  refine ⟨reduction program clock,reduction_isPolyTime program clock hrows,?_⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  exact (hsemantic x).symm

/-- Uniform polynomial generation of the explicitly specified finite table
rows discharges SAT hardness; all other premises are already proved above. -/
theorem sat_hard_of_uniform_rows
    (hrows : ∀ (program : Program) (clock : Polynomial Nat),
      ComplexityTheory.IsPolyTime (tableRows program clock)) :
    Shared.ComplexityBridge.CanonicalClasses.PolyRed Shared.ComplexityBridge.CNF.sat
      Source284CanonicalConditional.referenceLanguage := by
  obtain ⟨program,clock,_,hsemantic⟩ := sat_reference_frame
  exact sat_hard_of_rows program clock (hrows program clock) hsemantic

end Shared.Beeping.NPcoNP.Source284SATReferenceFrame
