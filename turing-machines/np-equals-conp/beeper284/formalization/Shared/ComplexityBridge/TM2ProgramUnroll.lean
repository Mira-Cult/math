import Shared.ComplexityBridge.TM2ProgramOutputs
import Shared.ComplexityBridge.TM2CircuitIterationRun

set_option backward.isDefEq.respectTransparency false

/-! Assemble the fixed-program transition template and its outputs into the
charged polynomial-time unroller. Both window and clock are unary lists. -/
namespace Shared.ComplexityBridge.TM2ProgramUnroll
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CircuitCNF
open Shared.ComplexityBridge.CircuitProgramMove
open Shared.Codes.FinitePrograms

abbrev Input := List Bool × List Bool

def widthTokens (program : Program) (tokens : List Bool) : List Bool :=
  TM2CircuitOutputWorker.constantTokens (program.length+1) tokens ++ TM2CircuitOutputWorker.copies 2 tokens

theorem widthTokens_length (program : Program) (tokens : List Bool) :
    (widthTokens program tokens).length = inputWidth program tokens.length := by
  simp [widthTokens,TM2CircuitOutputWorker.constantTokens_length,TM2CircuitOutputWorker.copies_length,inputWidth]
  omega

theorem widthTokens_isPolyTime (program : Program) : ComplexityTheory.IsPolyTime (widthTokens program) :=
  TM2CircuitTemplate.append_isPolyTime (TM2CircuitOutputWorker.constantTokens (program.length+1)) (TM2CircuitOutputWorker.copies 2)
    (TM2CircuitOutputWorker.constantTokens_isPolyTime _) (TM2CircuitOutputWorker.copies_isPolyTime 2)

def request (program : Program) (p : Input) : TM2CircuitIteration.Work × List Bool :=
  let width := widthTokens program p.1
  let base := width.length
  let moveArgs := (p.1,base)
  let gs := TM2ProgramMove.continuing program moveArgs
  let outs := TM2ProgramOutputs.outputs program moveArgs
  let refs := TM2UnaryRange.rangeFromTokens width
  ((((width,gs),outs),(base,refs,[])),p.2)

theorem request_isPolyTime (program : Program) : ComplexityTheory.IsPolyTime (request program) := by
  let tokens : Input → List Bool := fun p => p.1
  let clock : Input → List Bool := fun p => p.2
  let width : Input → List Bool := fun p => widthTokens program (tokens p)
  let base : Input → Nat := fun p => (width p).length
  let args : Input → TM2ProgramMove.Input := fun p => (tokens p,base p)
  let gates : Input → List Gate := fun p => TM2ProgramMove.continuing program (args p)
  let outputs : Input → List Nat := fun p => TM2ProgramOutputs.outputs program (args p)
  let refs : Input → List Nat := fun p => TM2UnaryRange.rangeFromTokens (width p)
  let empty : Input → List Gate := fun _ => []
  let params : Input → TM2CircuitIteration.Parameters := fun p => ((width p,gates p),outputs p)
  let state : Input → TM2CircuitIteration.State := fun p => (base p,refs p,empty p)
  let work : Input → TM2CircuitIteration.Work := fun p => (params p,state p)
  have ht : ComplexityTheory.IsPolyTime tokens := TM2PairFirst.first_isPolyTime
  have hc : ComplexityTheory.IsPolyTime clock := TM2GuardAllStep.second_isPolyTime
  have hw : ComplexityTheory.IsPolyTime width := TM2Compose.isPolyTime_comp tokens (widthTokens program) ht (widthTokens_isPolyTime program)
  have hb : ComplexityTheory.IsPolyTime base := TM2Compose.isPolyTime_comp width List.length hw TM2BinaryListLength.length_isPolyTime
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime tokens base ht hb
  have hg : ComplexityTheory.IsPolyTime gates := TM2Compose.isPolyTime_comp args (TM2ProgramMove.continuing program) ha (TM2ProgramMove.continuing_isPolyTime program)
  have ho : ComplexityTheory.IsPolyTime outputs := TM2Compose.isPolyTime_comp args (TM2ProgramOutputs.outputs program) ha (TM2ProgramOutputs.outputs_isPolyTime program)
  have hr : ComplexityTheory.IsPolyTime refs := TM2Compose.isPolyTime_comp width TM2UnaryRange.rangeFromTokens hw TM2UnaryRange.rangeFromTokens_isPolyTime
  have he : ComplexityTheory.IsPolyTime empty := TM2EmptyConstant.isPolyTime [] rfl
  have hp : ComplexityTheory.IsPolyTime params := TM2GuardAllStep.pair_isPolyTime (fun p => (width p,gates p)) outputs
    (TM2GuardAllStep.pair_isPolyTime width gates hw hg) ho
  have hs : ComplexityTheory.IsPolyTime state := TM2GuardAllStep.pair_isPolyTime base (fun p => (refs p,empty p)) hb
    (TM2GuardAllStep.pair_isPolyTime refs empty hr he)
  have hwork : ComplexityTheory.IsPolyTime work := TM2GuardAllStep.pair_isPolyTime params state hp hs
  have h := TM2GuardAllStep.pair_isPolyTime work clock hwork hc
  change ComplexityTheory.IsPolyTime (request program) at h
  exact h

def gates (program : Program) (p : Input) : List Gate := TM2CircuitIterationRun.gatesWorker (request program p)
def refs (program : Program) (p : Input) : List Nat := TM2CircuitIterationRun.refsWorker (request program p)

theorem workers_isPolyTime (program : Program) : ComplexityTheory.IsPolyTime (gates program) ∧ ComplexityTheory.IsPolyTime (refs program) := by
  exact ⟨TM2Compose.isPolyTime_comp (request program) TM2CircuitIterationRun.gatesWorker (request_isPolyTime program)
      TM2CircuitIterationRun.workers_isPolyTime.1,
    TM2Compose.isPolyTime_comp (request program) TM2CircuitIterationRun.refsWorker (request_isPolyTime program)
      TM2CircuitIterationRun.workers_isPolyTime.2⟩

theorem workers_correct (program : Program) (tokens clock : List Bool) :
    let k := tokens.length
    let width := inputWidth program k
    let gs := continuingGates program k width
    let outs := continuingOutputs program k width
    gates program (tokens,clock) = CircuitRelocate.unroll width gs outs width (List.range width) clock.length ∧
    refs program (tokens,clock) = CircuitRelocate.finalRefs width gs outs width (List.range width) clock.length := by
  let width := widthTokens program tokens
  let base := width.length
  let gs := continuingGates program tokens.length base
  let outs := continuingOutputs program tokens.length base
  have hw : base = inputWidth program tokens.length := widthTokens_length program tokens
  have hv : validGates width.length gs := by
    change validGates base (continuingGates program tokens.length base)
    apply continuingGates_valid
    omega
  have ho : ∀ o ∈ outs, o < width.length+gs.length := by
    intro o hm
    have h := continuingOutputs_bound program tokens.length base (by omega) o hm
    exact h
  have h := TM2CircuitIterationRun.workers_correct width gs outs base (List.range base) clock hv ho
  simpa [gates,refs,request,TM2ProgramMove.continuing,TM2ProgramOutputs.outputs_correct,
    TM2UnaryRange.rangeFromTokens,width,base,gs,outs,hw] using h

namespace Fixtures
example : gates [] ([],[]) = [] := rfl
end Fixtures
end Shared.ComplexityBridge.TM2ProgramUnroll
