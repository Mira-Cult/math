import Shared.PNP.Record285.ReferenceSerialization
import Shared.ComplexityBridge.TM2BoundedUnary
import Shared.ComplexityBridge.TM2UnaryPolynomialIO

/-! Uniform row expansion and padding for the exact 285-state reference
frame. The remaining conditional premise is production of the binary-valued
transition-record list, including the public-prefix loader and relocation. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

noncomputable section

namespace Shared.PNP.Record285.ReferenceRowBudget
open Shared.PNP.Record285.UnaryProgram
open Shared.PNP.Record285.UnaryReferenceTail
open Shared.PNP.Record285.CanonicalInput
open Shared.PNP.Record285.HardwireFiniteVerifier
open Shared.PNP.Record285.ReferenceSerialization
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge

/-- Expand each binary record only up to an explicitly provided unary budget. -/
def rowTokens (input : List Bool × List Nat) : List (List Bool) :=
  input.2.map (fun n => TM2BoundedUnary.expand (input.1,n))

theorem rowTokens_isPolyTime : ComplexityTheory.IsPolyTime rowTokens := by
  exact TM2ContextMapGeneric.contextMap_isPolyTime TM2BoundedUnary.expand
    TM2BoundedUnary.expand_isPolyTime

theorem rowTokens_lengths (fuel : List Bool) (rows : List Nat)
    (h : ∀ n ∈ rows, n ≤ fuel.length) :
    (rowTokens (fuel,rows)).map List.length = rows := by
  simp only [rowTokens,List.map_map,Function.comp_def]
  calc
    _ = rows.map id := by
      apply List.map_congr_left
      intro n hn
      simp [TM2BoundedUnary.expand_correct,Nat.min_eq_left (h n hn)]
    _ = rows := List.map_id rows

/-- Every packed row is bounded, including HALT targets, for every finite
table and both choice bits. -/
theorem tableRecords_bounded (n : Nat) (f : Fin n → Bool → Bool → FiniteAction n)
    (a : Nat) (ha : a ∈ tableRecords n f) : a ≤ 16*n+7 := by
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  unfold finiteRows at hb
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hb
  subst b
  exact lower_pack_bound n _

/-- The state count of the loader followed by the fixed finite verifier. -/
def statePolynomial (p : Program) (witness : Polynomial Nat) : Polynomial Nat :=
  Polynomial.C 2 * (Polynomial.X+witness) + Polynomial.C (2+states p)

def rowPolynomial (p : Program) (witness : Polynomial Nat) : Polynomial Nat :=
  Polynomial.C 16 * statePolynomial p witness + Polynomial.C 7

def paddingPolynomial (witness budget : Polynomial Nat) : Polynomial Nat :=
  budget + Polynomial.C 2 * (Polynomial.X+witness) + Polynomial.C 2

theorem statePolynomial_eval (p : Program) (witness : Polynomial Nat) (input : List Bool) :
    (statePolynomial p witness).eval input.length =
      Shared.PNP.Record285.ChoiceLoader.offset (input.length+witness.eval input.length)+states p := by
  simp [statePolynomial,Shared.PNP.Record285.ChoiceLoader.offset,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_X]
  omega

theorem rowPolynomial_eval (p : Program) (witness : Polynomial Nat) (input : List Bool) :
    (rowPolynomial p witness).eval input.length =
      16*(Shared.PNP.Record285.ChoiceLoader.offset (input.length+witness.eval input.length)+states p)+7 := by
  simp only [rowPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    statePolynomial_eval]

theorem paddingPolynomial_eval (witness budget : Polynomial Nat) (input : List Bool) :
    (paddingPolynomial witness budget).eval input.length =
      budget.eval input.length+Shared.PNP.Record285.ChoiceLoader.offset (input.length+witness.eval input.length) := by
  simp [paddingPolynomial,Shared.PNP.Record285.ChoiceLoader.offset,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_X]
  omega

/-- The exact finite-table records, in the four-selector order used by the
source. The input-dependent table includes both the fixed public prefix and
relocated verifier. -/
def verifierRows (p : Program) (witness : Polynomial Nat) (input : List Bool) : List Nat :=
  tableRecords
    (Shared.PNP.Record285.ChoiceLoader.offset (input.length+witness.eval input.length)+states p)
    (Shared.PNP.Record285.HardwireChoiceLoader.table (input.length+witness.eval input.length) (states p)
      (states_positive p) input.length (value input) (relativeTable p))

def verifierRowTokens (p : Program) (witness : Polynomial Nat) (input : List Bool) : List (List Bool) :=
  rowTokens (TM2UnaryPolynomialIO.unaryPolynomial (rowPolynomial p witness) input,verifierRows p witness input)

def verifierPadding (witness budget : Polynomial Nat) (input : List Bool) : List Bool :=
  TM2UnaryPolynomialIO.unaryPolynomial (paddingPolynomial witness budget) input

theorem verifierRowTokens_lengths (p : Program) (witness : Polynomial Nat) (input : List Bool) :
    (verifierRowTokens p witness input).map List.length = verifierRows p witness input := by
  apply rowTokens_lengths
  intro n hn
  simp only [TM2UnaryPolynomialIO.unaryPolynomial,List.length_replicate,rowPolynomial_eval]
  exact tableRecords_bounded _ _ n hn

theorem verifierPadding_length (witness budget : Polynomial Nat) (input : List Bool) :
    (verifierPadding witness budget input).length =
      budget.eval input.length+Shared.PNP.Record285.ChoiceLoader.offset (input.length+witness.eval input.length) := by
  simp [verifierPadding,TM2UnaryPolynomialIO.unaryPolynomial,paddingPolynomial_eval]

theorem verifierPadding_isPolyTime (witness budget : Polynomial Nat) :
    ComplexityTheory.IsPolyTime (verifierPadding witness budget) :=
  TM2UnaryPolynomialIO.unaryPolynomial_isPolyTime (paddingPolynomial witness budget)

theorem verifierRowTokens_isPolyTime_of_rows (p : Program) (witness : Polynomial Nat)
    (hrows : ComplexityTheory.IsPolyTime (verifierRows p witness)) :
    ComplexityTheory.IsPolyTime (verifierRowTokens p witness) := by
  have hf := TM2UnaryPolynomialIO.unaryPolynomial_isPolyTime (rowPolynomial p witness)
  have hp := TM2GuardAllStep.pair_isPolyTime
    (TM2UnaryPolynomialIO.unaryPolynomial (rowPolynomial p witness)) (verifierRows p witness) hf hrows
  exact TM2Compose.isPolyTime_comp
    (fun input => (TM2UnaryPolynomialIO.unaryPolynomial (rowPolynomial p witness) input,verifierRows p witness input))
    rowTokens hp rowTokens_isPolyTime

/-- All costs after binary-row production are discharged. The only remaining
premise is a uniform polynomial-time builder of the exact transition records;
no assumption about P = NP is introduced. -/
theorem verifierFrame_isPolyTime_of_rows (p : Program) (witness budget : Polynomial Nat)
    (hrows : ComplexityTheory.IsPolyTime (verifierRows p witness)) :
    ComplexityTheory.IsPolyTime (fun input => verifierReferenceFrame p input
      (witness.eval input.length) (budget.eval input.length)) := by
  apply verifier_frame_isPolyTime_of_workers p
    (fun input => witness.eval input.length) (fun input => budget.eval input.length)
    (verifierRowTokens p witness) (verifierPadding witness budget)
    (verifierRowTokens_isPolyTime_of_rows p witness hrows) (verifierPadding_isPolyTime witness budget)
  · exact verifierRowTokens_lengths p witness
  · exact verifierPadding_length witness budget

/-- Total indexed row selector. The out-of-range result is zero; the frame
builder only asks for indices below four times the finite state count. -/
def verifierRecordAt (p : Program) (witness : Polynomial Nat) (request : List Bool × Nat) : Nat :=
  let input := request.1
  let i := request.2
  let k := input.length+witness.eval input.length
  let total := Shared.PNP.Record285.ChoiceLoader.offset k+states p
  if h : i < 4*total then
    pack (lower (Shared.PNP.Record285.HardwireChoiceLoader.table k (states p)
      (states_positive p) input.length (value input) (relativeTable p)
      ⟨i/4,by omega⟩ (decide ((i%4)/2=1)) (decide (i%2=1))))
  else 0

/-- Within the loader, the apparently large numeric public-input value is
only queried at a single bit. This equation exposes the exact list lookup,
including out-of-range behavior, and the packed live destination. -/
theorem verifierRecordAt_loader (p : Program) (witness : Polynomial Nat)
    (input : List Bool) (i : Nat)
    (hi : i < 4*(Shared.PNP.Record285.ChoiceLoader.offset (input.length+witness.eval input.length)+states p))
    (hq : i/4 < Shared.PNP.Record285.ChoiceLoader.offset (input.length+witness.eval input.length)) :
    verifierRecordAt p witness (input,i) =
      Shared.PNP.Record285.RelativeTape.bitVal
        (if i/4 < input.length+witness.eval input.length then
          if i/4 < input.length then (input[i/4]?).getD false else decide (i%2=1)
        else decide ((i%4)/2=1)) +
      2 * Shared.PNP.Record285.RelativeTape.bitVal
        (decide (i/4 = input.length+witness.eval input.length ∨
          i/4 = 2*(input.length+witness.eval input.length)+1)) +
      16*(i/4+1)+4 := by
  simp only [verifierRecordAt,hi, ↓reduceDIte,Shared.PNP.Record285.HardwireChoiceLoader.table,
    Shared.PNP.Record285.ChoiceLoader.table,hq,lower,Option.elim_some,pack,stateCode]
  rw [value_bit]
  omega

/-- Relocating a live target increases its packed record by sixteen times
the loader offset; a HALT target must remain zero and is not shifted. -/
theorem packed_relocate {n : Nat} (k : Nat) (a : FiniteAction n) :
    pack (lower ⟨a.write,a.turn,a.next.map (Shared.PNP.Record285.ChoiceLoader.relocate k)⟩) =
      pack (lower a) + if a.next.isSome then 16*Shared.PNP.Record285.ChoiceLoader.offset k else 0 := by
  cases a with
  | mk write turn next =>
    cases next with
    | none => simp [lower,pack]
    | some q =>
      simp [lower,pack,stateCode,Shared.PNP.Record285.ChoiceLoader.relocate]
      omega

/-- Beyond the loader, the row is a fixed verifier row with an exact live
state relocation. No public-input bit is read in this branch. -/
theorem verifierRecordAt_verifier (p : Program) (witness : Polynomial Nat)
    (input : List Bool) (i : Nat)
    (hi : i < 4*(Shared.PNP.Record285.ChoiceLoader.offset (input.length+witness.eval input.length)+states p))
    (hq : Shared.PNP.Record285.ChoiceLoader.offset (input.length+witness.eval input.length) ≤ i/4) :
    let k := input.length+witness.eval input.length
    let q : Fin (states p) := ⟨i/4-Shared.PNP.Record285.ChoiceLoader.offset k,by dsimp [k]; omega⟩
    let a := relativeTable p q (decide ((i%4)/2=1)) (decide (i%2=1))
    verifierRecordAt p witness (input,i) = pack (lower a) +
      if a.next.isSome then 16*Shared.PNP.Record285.ChoiceLoader.offset k else 0 := by
  dsimp only
  have hn : ¬ i/4 < Shared.PNP.Record285.ChoiceLoader.offset (input.length+witness.eval input.length) := by omega
  have hw : ¬ i/4 < input.length := by
    unfold Shared.PNP.Record285.ChoiceLoader.offset at hq
    omega
  simp only [verifierRecordAt,hi, ↓reduceDIte,Shared.PNP.Record285.HardwireChoiceLoader.table,
    hw, ↓reduceIte,Shared.PNP.Record285.ChoiceLoader.table,hn]
  exact packed_relocate _ _

/-- Out-of-range requests have a fixed, total convention. -/
theorem verifierRecordAt_outside (p : Program) (witness : Polynomial Nat) (input : List Bool) (i : Nat)
    (hi : 4*(Shared.PNP.Record285.ChoiceLoader.offset (input.length+witness.eval input.length)+states p) ≤ i) :
    verifierRecordAt p witness (input,i) = 0 := by
  simp [verifierRecordAt,show ¬ i < 4*(Shared.PNP.Record285.ChoiceLoader.offset
    (input.length+witness.eval input.length)+states p) by omega]

def rowCountPolynomial (p : Program) (witness : Polynomial Nat) : Polynomial Nat :=
  Polynomial.C 4 * statePolynomial p witness

theorem rowCountPolynomial_eval (p : Program) (witness : Polynomial Nat) (input : List Bool) :
    (rowCountPolynomial p witness).eval input.length =
      4*(Shared.PNP.Record285.ChoiceLoader.offset (input.length+witness.eval input.length)+states p) := by
  simp [rowCountPolynomial,Polynomial.eval_mul,statePolynomial_eval]

/-- Enumerating all ordinal selectors invokes exactly the original finite
record list, including the two read and two choice variants per state. -/
theorem verifierRows_eq_indexed (p : Program) (witness : Polynomial Nat) (input : List Bool) :
    verifierRows p witness input =
      (List.range ((rowCountPolynomial p witness).eval input.length)).map
        (fun i => verifierRecordAt p witness (input,i)) := by
  rw [rowCountPolynomial_eval]
  apply List.ext_getElem
  · simp [verifierRows,tableRecords,finiteRows]
  · intro i hleft hright
    have hi : i < 4*(Shared.PNP.Record285.ChoiceLoader.offset (input.length+witness.eval input.length)+states p) := by
      simpa [verifierRows,tableRecords,finiteRows] using hleft
    simp [verifierRows,tableRecords,finiteRows,verifierRecordAt,hi]

/-- The list traversal, range construction and all output serialization are
paid; only the fixed program's single indexed row selector is still assumed
to have a polynomial-time canonical implementation. -/
theorem verifierRows_isPolyTime_of_recordAt (p : Program) (witness : Polynomial Nat)
    (hrow : ComplexityTheory.IsPolyTime (verifierRecordAt p witness)) :
    ComplexityTheory.IsPolyTime (verifierRows p witness) := by
  let indices : List Bool → List Nat := fun input =>
    TM2UnaryRange.rangeFromTokens (TM2UnaryPolynomialIO.unaryPolynomial (rowCountPolynomial p witness) input)
  have hi : ComplexityTheory.IsPolyTime indices := TM2Compose.isPolyTime_comp
    (TM2UnaryPolynomialIO.unaryPolynomial (rowCountPolynomial p witness)) TM2UnaryRange.rangeFromTokens
    (TM2UnaryPolynomialIO.unaryPolynomial_isPolyTime (rowCountPolynomial p witness))
    TM2UnaryRange.rangeFromTokens_isPolyTime
  have hp := TM2GuardAllStep.pair_isPolyTime (fun input : List Bool => input) indices
    ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩ hi
  have hc := TM2Compose.isPolyTime_comp (fun input => (input,indices input))
    (TM2ContextMapGeneric.contextMap (verifierRecordAt p witness)) hp
    (TM2ContextMapGeneric.contextMap_isPolyTime (verifierRecordAt p witness) hrow)
  have he : (fun input => TM2ContextMapGeneric.contextMap (verifierRecordAt p witness) (input,indices input)) =
      verifierRows p witness := by
    funext input
    simpa [TM2ContextMapGeneric.contextMap,indices,TM2UnaryRange.rangeFromTokens,
      TM2UnaryPolynomialIO.unaryPolynomial] using (verifierRows_eq_indexed p witness input).symm
  rw [he] at hc
  exact hc

theorem verifierFrame_isPolyTime_of_recordAt (p : Program) (witness budget : Polynomial Nat)
    (hrow : ComplexityTheory.IsPolyTime (verifierRecordAt p witness)) :
    ComplexityTheory.IsPolyTime (fun input => verifierReferenceFrame p input
      (witness.eval input.length) (budget.eval input.length)) :=
  verifierFrame_isPolyTime_of_rows p witness budget (verifierRows_isPolyTime_of_recordAt p witness hrow)

end Shared.PNP.Record285.ReferenceRowBudget
