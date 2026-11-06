import Shared.Beeping.NPcoNP.NativeAllBankDecrementPadding
import Shared.Beeping.NPcoNP.Grammar284DecrementSuccessor
import Shared.Beeping.NPcoNP.Grammar284OrdinaryPhysical
import Shared.Beeping.NPcoNP.Grammar284OrdinaryPreparation

/-! An arbitrary suffix survives a positive decrement through the contracted
physical graph step under the supplied prepared bank layout. -/
namespace Shared.Beeping.NPcoNP.Grammar284PositiveTailFrame
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch
open Shared.Beeping.NPcoNP.NativeGrammarSelectorDispatch
open Shared.Beeping.NPcoNP.Grammar284ExpansionPaths
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.NativeAllBankDecrementPadding
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284GraphOperation
open Shared.Beeping.NPcoNP.Grammar284BankCorrespondence
open Shared.Beeping.NPcoNP.Grammar284PhysicalSuccessor
open Shared.Beeping.NPcoNP.Grammar284OrdinaryPhysical
open Shared.Beeping.NPcoNP.Grammar284OrdinaryContraction
open Shared.Beeping.NPcoNP.Grammar284OrdinaryPreparation
open Shared.Beeping.NPcoNP.Grammar284DecrementSuccessor
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

theorem positive_to_first_successor_frame (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,false))
    (graph : Bank 12) (values graphTail more : List Nat) (value : Nat) (pad : List Bool)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++(value+1)::graphTail)
    (origin h separator : Int) (t : Int → Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (hlong : h+4≤separator)
    (room : origin+55<separator) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (marker : t h=true)
    (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (control : ∀ q, h+3≤q → q<separator → t q=true) (delimiter : t separator=false)
    (bank : Holds t (separator+1)
      ((encode values ++ (encode ((value+1)::(graphTail++more)) ++ [false,false])) ++ pad)) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (dst : Nat) (next : Path) (nextName : String) (steps : Nat) (out : Int → Bool),
      successor traceState557.acc.starts path 0=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧
      0<steps ∧ result.2=[] ∧ result.1.state=target.code[state].yes ∧
      Holds out origin next ∧ Holds out (separator+1) ((encode (arrayBank result.1.bank++more++[0]) ++ [false]) ++ pad) ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((next.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out separator=false ∧ out (separator-1)=true ∧
      (∀ q, separator+1+((encode (arrayBank result.1.bank++more++[0])).length : Int)≤q → out q=t q) ∧
      silentSegment machine (cfg (operationAt n false) h t) (cfg 93 (origin+1) out) steps := by
  dsimp only
  let pos := separator+1+((encode values).length : Int)
  have gstep := graph_decrement_positive_step state path name leaf n operation graph values graphTail value hlen layout
  have gbank : arrayBank (target.system.step ⟨state,graph⟩).1.bank=values++value::graphTail := by
    rw [gstep]
    exact write_selected_array graph n values graphTail (value+1) value hlen layout
  obtain ⟨a,mid,ha,hbank,hzero,hzero1,hmark,hcontrol,hsep,hframe,hfar,hseg⟩ :=
    positive_to1_padded n h separator t values value (graphTail++more) pad hlen hlong marker z1 z2 control delimiter bank
  have hmidword : Holds mid origin path := by
    apply holds_transport t mid origin path word
    intro q hq hq'
    exact (hframe q (by omega) (by omega) (by omega)).symm
  have hmidleft : ∀ q, q<origin → mid q=false := by
    intro q hq
    rw [hframe q (by omega) (by omega) (by omega)]
    exact left q hq
  have hbetween : ∀ q, h-1<q → q<h+2 → mid q=false := by
    intro q hq hq'
    have he : q=h ∨ q=h+1 := by omega
    rcases he with rfl | rfl
    · exact hzero
    · exact hzero1
  obtain ⟨dst,next,nextName,b,out,hsucc,hnext,_hwalk,hb,hnextWord,houtleft,houtgap,houtsep,hright,hbankFrame,hcarry⟩ :=
    carry_to_first_successor_exact state path name leaf notRoot n false operation 0 (Or.inl rfl)
      (by intro _; rfl) mid origin (h-1) (h+2) separator (by simp [hentry]) room hmidword hmidleft
      (by omega) hmark hbetween (by omega)
      (by intro q hq hq'; exact hcontrol q (by omega) hq') hsep
  have houtbank : Holds out (separator+1)
      ((encode values ++ (encode (value::(graphTail++more)) ++ [true,false,false])) ++ pad) := by
    apply holds_transport mid out (separator+1) _ hbank
    intro q hq _
    exact (hbankFrame q (by omega)).symm
  refine ⟨dst,next,nextName,a+b,out,hsucc,hnext,by omega,?_,?_,hnextWord,?_,houtleft,houtgap,houtsep,hright,?_,?_⟩
  · simp only [gstep]
  · simp only [gstep]
  · rw [gbank]
    simpa [encode_append,encode,block,List.append_assoc] using houtbank
  · intro q hq
    rw [gbank] at hq
    have hlimit : pos+2+((List.replicate value true ++ (graphTail++more).flatMap
        (fun z => false :: List.replicate (z+1) true)).length : Int)<q := by
      simp only [flat_length,encode_append,List.length_append,List.length_replicate,
        encode,block_length,List.length_cons,List.length_nil,Nat.cast_add] at *
      dsimp [pos] at *
      push_cast at *
      omega
    rw [hbankFrame q (by omega),hfar q hlimit]
  · exact segAdd machine _ _ _ a b hseg hcarry


#print axioms positive_to_first_successor_frame
end Shared.Beeping.NPcoNP.Grammar284PositiveTailFrame
