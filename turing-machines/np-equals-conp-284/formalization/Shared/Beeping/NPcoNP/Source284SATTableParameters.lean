import Shared.Beeping.NPcoNP.Source284SATReferenceFrame
import Shared.Beeping.NPcoNP.Source284ConstantEncodedRowsTM2
import Shared.ComplexityBridge.TM2BoundedSubtract
import Shared.ComplexityBridge.GeneratorFamilyBridge

/-! Canonical polynomial-time parameters for the SAT validator table.
These are inputs to the remaining row generator, not the row generator itself. -/
namespace Shared.Beeping.NPcoNP.Source284SATTableParameters

open ComplexityTheory Shared.ComplexityBridge
open Shared.Codes.FinitePrograms (Program)
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284PairPrefixLoader (pairPrefix)
open Shared.Beeping.NPcoNP.Source284SATWindowClock

/-- The number of grammar steps is the total window less the already-scanned
public prefix. The subtraction is implemented on explicitly supplied unary
lists and therefore charges their full bit length. -/
def grammarTokens (clock : Polynomial Nat) (x : List Bool) : List Bool :=
  TM2BoundedSubtract.suffix (windowTokens clock 1 x) (pairPrefix x)

theorem pairPrefix_isPolyTime : IsPolyTime pairPrefix := by
  change IsPolyTime Shared.ComplexityBridge.CircuitPairWitness.pairPrefix
  exact GeneratorFamilyBridge.pairPrefix_isPolyTime

theorem grammarTokens_length (clock : Polynomial Nat) (x : List Bool) :
    (grammarTokens clock x).length =
      (windowTokens clock 1 x).length - (pairPrefix x).length := by
  simp [grammarTokens,TM2BoundedSubtract.suffix_correct]

theorem grammarTokens_isPolyTime (clock : Polynomial Nat) : IsPolyTime (grammarTokens clock) := by
  have hw : IsPolyTime (windowTokens clock 1) := window_isPolyTime clock 1
  have hp : IsPolyTime pairPrefix := pairPrefix_isPolyTime
  have h := TM2Compose.isPolyTime_comp (fun x => (windowTokens clock 1 x,pairPrefix x))
    (fun p : List Bool × List Bool => TM2BoundedSubtract.suffix p.1 p.2)
    (TM2GuardAllStep.pair_isPolyTime _ _ hw hp) TM2BoundedSubtract.suffix_isPolyTime
  exact h

/-- Inputs for a future row generator: the actual public prefix, unary
grammar clock, and the fixed verifier's explicit encoded rows. -/
def parameters (program : Program) (clock : Polynomial Nat) (x : List Bool) :
    List Bool × (List Bool × EncRows) :=
  (pairPrefix x,(grammarTokens clock x,encodeRows (Source284FiniteRelativeRows.rows program)))

theorem parameters_isPolyTime (program : Program) (clock : Polynomial Nat) :
    IsPolyTime (parameters program clock) := by
  have hrows : IsPolyTime (fun _ : List Bool => encodeRows (Source284FiniteRelativeRows.rows program)) :=
    Source284ConstantEncodedRowsTM2.constRows_isPolyTime _
  exact TM2GuardAllStep.pair_isPolyTime pairPrefix
    (fun x => (grammarTokens clock x,encodeRows (Source284FiniteRelativeRows.rows program)))
    pairPrefix_isPolyTime (TM2GuardAllStep.pair_isPolyTime _ _ (grammarTokens_isPolyTime clock) hrows)

/-- Concrete finite-row construction from the three explicitly encoded
parameters. Its canonical polynomial-time bound is the remaining obligation. -/
def produceRows (p : List Bool × (List Bool × EncRows)) : EncRows :=
  let expected := p.1
  let clock := p.2.1.length
  let original := Source284ListTables.table (decodeRows p.2.2)
  let validator := Source284VerifierHandoff.table expected clock original
  Source284MaterializeRows.rows
    (Source284CertificateDispatch.allocated expected clock + p.2.2.length + 1)
    (Source284FacingAdapter.table validator)

theorem produceRows_parameters (program : Program) (clock : Polynomial Nat) (x : List Bool) :
    produceRows (parameters program clock x) = Source284SATReferenceFrame.tableRows program clock x := by
  simp [produceRows,parameters,grammarTokens_length,Source284SATReferenceFrame.tableRows,
    Source284SATReferenceFrame.windowSize,Source284SATReferenceFrame.stateCount,
    Source284SATReferenceFrame.facedTable]

/-- A polynomial implementation of this concrete row producer is sufficient
to discharge the row-cost premise in the conditional controller theorem. -/
theorem tableRows_isPolyTime_of_producer
    (hproducer : IsPolyTime produceRows) (program : Program) (clock : Polynomial Nat) :
    IsPolyTime (Source284SATReferenceFrame.tableRows program clock) := by
  have h := TM2Compose.isPolyTime_comp (parameters program clock) produceRows
    (parameters_isPolyTime program clock) hproducer
  simpa only [produceRows_parameters] using h

end Shared.Beeping.NPcoNP.Source284SATTableParameters
