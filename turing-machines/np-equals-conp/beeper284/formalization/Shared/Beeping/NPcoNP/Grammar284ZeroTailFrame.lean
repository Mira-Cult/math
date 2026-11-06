import Shared.Beeping.NPcoNP.Grammar284PhysicalSuccessor
import Shared.Beeping.NPcoNP.Grammar284BankCorrespondence
import Shared.Beeping.NPcoNP.NativeGrammarSelectorDispatch
import Shared.Beeping.NPcoNP.NativeAllBankDecrementNext

/-! Ordinary decrement bank effects through the first expanded successor.
Administrative jumps, root return and reachable-window recurrence are separate. -/
namespace Shared.Beeping.NPcoNP.Grammar284ZeroTailFrame
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch
open Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch
open Shared.Beeping.NPcoNP.NativeGrammarSelectorDispatch
open Shared.Beeping.NPcoNP.Grammar284SuccessorShape
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.NativeAllBankDecrement
open Shared.Beeping.NPcoNP.NativeAllBankDecrementNext
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284ExpansionPaths
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284GraphOperation
open Shared.Beeping.NPcoNP.Grammar284BankCorrespondence
open Shared.Beeping.NPcoNP.Grammar284PhysicalSuccessor
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem zero_to_first_successor_frame (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,false))
    (graph : Bank 12) (values graphTail more : List Nat) (pad : List Bool)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++0::graphTail)
    (origin h separator : Int) (t : Int → Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (hlong : h+4≤separator)
    (room : origin+55<separator) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (marker : t h=true) (prev : t (h-1)=false)
    (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (control : ∀ q, h+3≤q → q<separator → t q=true) (delimiter : t separator=false)
    (bank : Holds t (separator+1) (encode (arrayBank graph++more) ++ pad)) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (dst : Nat) (next : Path) (nextName : String) (steps : Nat) (out : Int → Bool),
      successor traceState557.acc.starts path 1=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧
      0<steps ∧ result.2=[] ∧ result.1.state=target.code[state].no ∧
      Holds out origin next ∧ Holds out (separator+1) (encode (arrayBank result.1.bank++more) ++ pad) ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((next.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out separator=false ∧ out (separator-1)=true ∧
      (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg (operationAt n false) h t) (cfg 93 (origin+1) out) steps := by
  dsimp only
  have gstep := graph_decrement_zero_step state path name leaf n operation graph values graphTail hlen layout
  have hpathlen : 1≤path.length := by
    have member := graph_leaf_member state path name leaf
    have walk : PreparedWalk path (.op name) :=
      expanded_leaf_follows traceState557.acc producerExpand (path,name) member
    obtain ⟨raw,he,_⟩ := walk
    rw [he]
    simp [preparedPrefix]
  have hphysical : Holds t (separator+1)
      (encode values ++ (block 0 ++ (encode (graphTail++more) ++ pad))) := by
    have hb := bank
    rw [layout] at hb
    simpa [encode_append,encode,List.append_assoc] using hb
  obtain ⟨a,mid,ha,hmark,hsep,hzero,hzero1,hcontrol,hright,hframe,hseg⟩ :=
    zero_to1_exact n h separator t values (encode (graphTail++more) ++ pad)
      hlen hlong marker prev z1 z2 control delimiter hphysical
  have hmidword : Holds mid origin path := by
    apply holds_transport t mid origin path word
    intro q hq hq'
    exact (hframe q (by omega)).symm
  have hmidleft : ∀ q, q<origin → mid q=false := by
    intro q hq
    rw [hframe q (by omega)]
    exact left q hq
  have hprev : mid (h-1)=false := (hframe _ (by omega)).trans prev
  have hbetween : ∀ q, h-2<q → q<h+2 → mid q=false := by
    intro q hq hq'
    have he : q=h-1 ∨ q=h ∨ q=h+1 := by omega
    rcases he with rfl | rfl | rfl
    · exact hprev
    · exact hzero
    · exact hzero1
  obtain ⟨dst,next,nextName,b,out,hsucc,hnext,_hwalk,hb,hnextWord,houtleft,houtgap,houtsep,hmarkerRight,hbankFrame,hcarry⟩ :=
    carry_to_first_successor_exact state path name leaf notRoot n false operation 1 (Or.inr rfl)
      (by intro _; rfl) mid origin (h-2) (h+2) separator
      (by simp only [Nat.cast_sub hpathlen,Nat.cast_one]; omega) room hmidword hmidleft
      (by omega) hmark hbetween (by omega)
      (by intro q hq hq'; exact hcontrol q (by omega) hq') hsep
  have hmidbank : Holds mid (separator+1) (encode (arrayBank graph++more) ++ pad) := by
    apply holds_transport t mid (separator+1) _ bank
    intro q hq _
    exact (hright q (by omega)).symm
  have houtbank : Holds out (separator+1) (encode (arrayBank graph++more) ++ pad) := by
    apply holds_transport mid out (separator+1) _ hmidbank
    intro q hq _
    exact (hbankFrame q (by omega)).symm
  refine ⟨dst,next,nextName,a+b,out,hsucc,hnext,by omega,?_,?_,hnextWord,?_,houtleft,houtgap,houtsep,hmarkerRight,?_,?_⟩
  · simp only [gstep]
  · simp only [gstep]
  · simpa only [gstep] using houtbank
  · intro q hq
    exact (hbankFrame q hq).trans (hright q hq)
  · exact segAdd machine _ _ _ a b hseg hcarry


#print axioms zero_to_first_successor_frame
end Shared.Beeping.NPcoNP.Grammar284ZeroTailFrame
