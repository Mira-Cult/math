import Shared.ComplexityBridge.TM2BinaryListLength
import Shared.ComplexityBridge.TM2FixInputs

/-! Assemble the existing constrained circuit CNF from supplied template,
seed bits, output wire and gate list. All sizes are charged under the pinned
canonical encoding; circuit generation itself is not assumed here. -/
namespace Shared.ComplexityBridge.TM2ConstrainedCNF
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CNF
open Shared.ComplexityBridge.CircuitCNF

abbrev Input := (List Bool × List Bool) × (Nat × List Gate)

/-- The second input is unary witness-count tokens, not a binary bound. -/
def build (p : Input) : Formula :=
  CircuitPairWitness.constrainedFormula p.1.1 p.1.2.length p.2.1 p.2.2

theorem build_isPolyTime : ComplexityTheory.IsPolyTime build := by
  let left : Input → List Bool × List Bool := fun p => p.1
  let right : Input → Nat × List Gate := fun p => p.2
  let fixed : Input → List Bool := fun p => p.1.1
  let tokens : Input → List Bool := fun p => p.1.2
  let output : Input → Nat := fun p => p.2.1
  let gates : Input → List Gate := fun p => p.2.2
  let fixedLen : Input → Nat := fun p => (fixed p).length
  let count : Input → Nat := fun p => (tokens p).length
  let free : Input → Nat := fun p => 3*count p
  let offsetArgs : Input → Nat × Nat := fun p => (fixedLen p,free p)
  let offset : Input → Nat := fun p => CNFBinaryPairAdd.addPair (offsetArgs p)
  let shapeArgs : Input → Nat × List Bool := fun p => (fixedLen p,tokens p)
  let fixArgs : Input → Nat × List Bool := fun p => (0,fixed p)
  let compileArgs : Input → Nat × (Nat × List Gate) := fun p => (offset p,(output p,gates p))
  let shape : Input → Formula := fun p => TM2ShapeClauses.fromTokens (shapeArgs p)
  let fix : Input → Formula := fun p => CircuitCNF.fixInputs 0 (fixed p)
  let code : Input → Formula := fun p => CircuitCNF.compile (offset p) (output p) (gates p)
  have hl : ComplexityTheory.IsPolyTime left := TM2PairFirst.first_isPolyTime
  have hr : ComplexityTheory.IsPolyTime right := TM2GuardAllStep.second_isPolyTime
  have hf : ComplexityTheory.IsPolyTime fixed := TM2Compose.isPolyTime_comp left (fun p : List Bool × List Bool => p.1) hl TM2PairFirst.first_isPolyTime
  have ht : ComplexityTheory.IsPolyTime tokens := TM2Compose.isPolyTime_comp left (fun p : List Bool × List Bool => p.2) hl TM2GuardAllStep.second_isPolyTime
  have ho : ComplexityTheory.IsPolyTime output := TM2Compose.isPolyTime_comp right (fun p : Nat × List Gate => p.1) hr TM2PairFirst.first_isPolyTime
  have hg : ComplexityTheory.IsPolyTime gates := TM2Compose.isPolyTime_comp right (fun p : Nat × List Gate => p.2) hr TM2GuardAllStep.second_isPolyTime
  have hfl : ComplexityTheory.IsPolyTime fixedLen := TM2Compose.isPolyTime_comp fixed List.length hf TM2BinaryListLength.length_isPolyTime
  have hc : ComplexityTheory.IsPolyTime count := TM2Compose.isPolyTime_comp tokens List.length ht TM2BinaryListLength.length_isPolyTime
  have hfree : ComplexityTheory.IsPolyTime free := TM2Compose.isPolyTime_comp count (fun n : Nat => 3*n) hc TM2ShapeClauses.triple_isPolyTime
  have hargs : ComplexityTheory.IsPolyTime offsetArgs := TM2GuardAllStep.pair_isPolyTime fixedLen free hfl hfree
  have hoff : ComplexityTheory.IsPolyTime offset := TM2Compose.isPolyTime_comp offsetArgs CNFBinaryPairAdd.addPair hargs CNFBinaryPairAdd.addPair_isPolyTime
  have hsargs : ComplexityTheory.IsPolyTime shapeArgs := TM2GuardAllStep.pair_isPolyTime fixedLen tokens hfl ht
  have hs : ComplexityTheory.IsPolyTime shape := TM2Compose.isPolyTime_comp shapeArgs TM2ShapeClauses.fromTokens hsargs TM2ShapeClauses.fromTokens_isPolyTime
  have hz : ComplexityTheory.IsPolyTime (fun _ : Input => (0 : Nat)) := TM2EmptyConstant.zero_isPolyTime
  have hfixargs : ComplexityTheory.IsPolyTime fixArgs := TM2GuardAllStep.pair_isPolyTime (fun _ : Input => 0) fixed hz hf
  have hfix : ComplexityTheory.IsPolyTime fix := TM2Compose.isPolyTime_comp fixArgs
    (fun p : Nat × List Bool => CircuitCNF.fixInputs p.1 p.2) hfixargs TM2FixInputs.fixInputs_isPolyTime
  have hcompilerargs : ComplexityTheory.IsPolyTime compileArgs := TM2GuardAllStep.pair_isPolyTime offset
    (fun p => (output p,gates p)) hoff (TM2GuardAllStep.pair_isPolyTime output gates ho hg)
  have hcode : ComplexityTheory.IsPolyTime code := TM2Compose.isPolyTime_comp compileArgs
    (fun p : Nat × (Nat × List Gate) => CircuitCNF.compile p.1 p.2.1 p.2.2) hcompilerargs TM2GateFoldLoop.compile_isPolyTime
  have h := TM2GateDispatch.append_isPolyTime shape (fun p => fix p ++ code p) hs
    (TM2GateDispatch.append_isPolyTime fix code hfix hcode)
  have he : (fun p => shape p ++ (fix p ++ code p)) = build := by
    funext p
    simp [shape,shapeArgs,TM2ShapeClauses.fromTokens_correct,fix,code,offset,offsetArgs,
      fixedLen,free,count,CNFBinaryPairAdd.addPair,build,CircuitPairWitness.constrainedFormula,
      CircuitCNF.compileFixed,fixed,tokens,output,gates]
  rw [he] at h
  exact h

namespace Fixtures
example : build (([],[]),(0,[])) = [[(0,true)]] := rfl
example : build (([true],[false]),(4,[])) =
    [[(1,true)],[(3,false)],[(0,true)],[(4,true)]] := rfl
end Fixtures
end Shared.ComplexityBridge.TM2ConstrainedCNF
