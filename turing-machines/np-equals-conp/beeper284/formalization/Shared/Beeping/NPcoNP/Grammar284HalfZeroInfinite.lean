import Shared.Beeping.NPcoNP.Grammar284HalfZeroSuccessor
import Shared.Beeping.NPcoNP.Grammar284OrdinaryPhysical
import Shared.Beeping.NPcoNP.Grammar284InfiniteIncrement

/-! A supplied prepared zero-HALF return and a checked graph contraction
preserve an infinite blank-tail parser window. This theorem does not supply
the local return, graph branch, preparation or reachability hypotheses. -/
namespace Shared.Beeping.NPcoNP.Grammar284HalfZeroInfinite
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284ExpansionPaths
open Shared.Beeping.NPcoNP.Grammar284SuccessorShapeBase
open Shared.Beeping.NPcoNP.Grammar284SuccessorShape
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.Grammar284HalfZeroSuccessor
open Shared.Beeping.NPcoNP.Grammar284OrdinaryPhysical
open Shared.Beeping.NPcoNP.Grammar284InfiniteIncrement
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 30000000

/-- The prepared physical zero branch reaches a matching graph successor with
its entire blank tail intact, under explicit local-return, graph-step and
contraction hypotheses. -/
theorem prepared_zero_step (row nextState : Fin 185) (dst : Nat)
    (path : Path) (name : String) (graph : Bank 12) (more : List Nat)
    (leaf : graphLeaf row=some (path,name))
    (hshape : successorShape path 1=true) (hrightmost : rightmostOK path 1=true)
    (hlast : path.getLast?=some false) (hsucc : successor traceState557.acc.starts path 1=some dst)
    (targetAt : Grammar284.target producerFullRows producerNumbering.map 3 dst=some nextState.val)
    (graphStep : target.system.step ⟨row,graph⟩=(⟨nextState,graph⟩,[]))
    (origin h separator : Int) (t : Int → Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (space : h+4≤separator)
    (room : origin+59≤separator) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (marker : t h=true)
    (z1 : t (h+1)=false) (control : ∀ q, h+2≤q → q<separator → t q=true)
    (sep : t separator=false) (bank : Holds t (separator+1) (encode (arrayBank graph++more)))
    (tail : ∀ q, separator+1+((encode (arrayBank graph++more)).length : Int)≤q → t q=false)
    (zeroReturn : t (h-1)=false →
      ∃ steps : Nat, 0<steps ∧ Holds (clearAt h t) (separator+1) (encode (arrayBank graph++more)) ∧
      (∀ q, q≠h → clearAt h t q=t q) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 1 (h-2) (clearAt h t)) steps) :
    ∃ steps out, 0<steps ∧ (target.system.step ⟨row,graph⟩).2=[] ∧
      InfiniteWindow (target.system.step ⟨row,graph⟩).1.state
        (target.system.step ⟨row,graph⟩).1.bank origin separator out ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  obtain ⟨next,nextName,a,mid,hnext,ha,hw,hl,hgap,hsep,hmark,hbank,hframe,hsegment⟩ :=
    prepared_zero_to_first_successor_frame row dst path name leaf hshape hrightmost hlast hsucc
      origin h separator t (encode (arrayBank graph++more)) hentry space (by omega)
      word left marker z1 control sep bank zeroReturn
  obtain ⟨total,last,out,htotal,hgraph,hout,houtleft,houtgap,houtmark,houtsep,houtbank,houtframe,hfinal⟩ :=
    finish_contraction_frame (cfg 93 (origin+1) t) a mid origin separator dst next nextName nextState
      targetAt hnext ha hsegment hw hl hgap (by omega) hmark hsep _ hbank
  have houttail : ∀ q, separator+1+((encode (arrayBank graph++more)).length : Int)≤q → out q=false := by
    intro q hq
    rw [houtframe q (by omega),hframe q (by omega)]
    exact tail q hq
  rw [graphStep]
  refine ⟨total,out,htotal,rfl,?_,hfinal⟩
  exact ⟨last.1,last.2,more,by simpa using hgraph,room,hout,houtleft,houtgap,houtmark,houtsep,houtbank,houttail⟩

#print axioms prepared_zero_step
end Shared.Beeping.NPcoNP.Grammar284HalfZeroInfinite
