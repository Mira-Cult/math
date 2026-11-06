import Shared.Beeping.NPcoNP.NativeAllBankIncrementPadding
import Shared.Beeping.NPcoNP.Grammar284IncrementSuccessor
import Shared.Beeping.NPcoNP.Grammar284OrdinaryPhysical
import Shared.Beeping.NPcoNP.Grammar284OrdinaryPreparation

/-! Preserve an arbitrary suffix through an increment and its first expanded
successor under an explicit prepared operation window. -/
namespace Shared.Beeping.NPcoNP.Grammar284IncrementTailFrame
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
open Shared.Beeping.NPcoNP.NativeAllBankIncrementPadding
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284GraphOperation
open Shared.Beeping.NPcoNP.Grammar284BankCorrespondence
open Shared.Beeping.NPcoNP.Grammar284PhysicalSuccessor
open Shared.Beeping.NPcoNP.Grammar284OrdinaryPhysical
open Shared.Beeping.NPcoNP.Grammar284OrdinaryContraction
open Shared.Beeping.NPcoNP.Grammar284OrdinaryPreparation
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem increment_to_first_successor_frame (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,true))
    (graph : Bank 12) (values graphTail more : List Nat) (value : Nat) (pad : List Bool)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++value::graphTail)
    (origin h : Int) (t : Int → Bool) (k : Nat)
    (hentry : h=origin+((path.length : Nat) : Int)) (hk : 0<k)
    (room : origin+55<h+3+(k : Int)) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (marker : t h=true)
    (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (control : ∀ i : Nat, i<k → t (h+3+(i : Int))=true)
    (delimiter : t (h+3+(k : Int))=false)
    (bank : Holds t (h+4+(k : Int))
      ((encode (values++value::(graphTail++more)) ++ [false]) ++ pad)) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (dst : Nat) (next : Path) (nextName : String) (steps : Nat) (out : Int → Bool),
      successor traceState557.acc.starts path 0=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧
      0<steps ∧ result.2=[] ∧ result.1.state=target.code[state].yes ∧
      Holds out origin next ∧ Holds out (h+4+(k : Int)) (encode (arrayBank result.1.bank++more) ++ pad) ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((next.length : Nat) : Int)-1<q → q<h+3+(k : Int)-1 → out q=false) ∧
      out (h+3+(k : Int))=false ∧ out (h+3+(k : Int)-1)=true ∧
      (∀ q, h+4+(k : Int)+((encode (arrayBank result.1.bank++more)).length : Int)≤q → out q=t q) ∧
      silentSegment machine (cfg (operationAt n true) h t) (cfg 93 (origin+1) out) steps := by
  dsimp only
  let separator := h+3+(k : Int)
  let pos := separator+1+((encode values).length : Int)
  have gstep := graph_increment_step state path name leaf n operation graph values graphTail value hlen layout
  have gbank : arrayBank (target.system.step ⟨state,graph⟩).1.bank=values++(value+1)::graphTail := by
    rw [gstep]
    exact write_selected_array graph n values graphTail value (value+1) hlen layout
  obtain ⟨a,mid,ha,hbank,hzero,hzero1,hmark,hcontrol,hsep,hframe,hseg⟩ :=
    increment_to1_padded n h t k values value (graphTail++more) pad marker hlen hk z1 z2 control delimiter bank
  have hmidword : Holds mid origin path := by
    apply holds_transport t mid origin path word
    intro q hq hq'
    have he : mid q=clearAt h t q := hframe q (by omega) (Or.inl (by omega))
    rw [he]
    simp [clearAt,show q≠h by omega]
  have hmidleft : ∀ q, q<origin → mid q=false := by
    intro q hq
    have he : mid q=clearAt h t q := hframe q (by omega) (Or.inl (by omega))
    rw [he]
    simpa [clearAt,show q≠h by omega] using left q hq
  have hbetween : ∀ q, h-1<q → q<h+2 → mid q=false := by
    intro q hq hq'
    have he : q=h ∨ q=h+1 := by omega
    rcases he with rfl | rfl
    · exact hzero
    · exact hzero1
  obtain ⟨dst,next,nextName,b,out,hsucc,hnext,_hwalk,hb,hnextWord,houtleft,houtgap,houtsep,hright,hbankFrame,hcarry⟩ :=
    carry_to_first_successor_exact state path name leaf notRoot n true operation 0 (Or.inl rfl)
      (by intro impossible; omega) mid origin (h-1) (h+2) separator
      (by simp [hentry]) (by simpa [separator] using room) hmidword hmidleft
      (by omega) hmark hbetween (by dsimp [separator]; omega)
      (by intro q hq hq'; exact hcontrol q (by omega) (by simpa only [separator] using hq'))
      (by simpa only [separator] using hsep)
  have houtbank : Holds out (separator+1) (encode (values++(value+1)::(graphTail++more)) ++ pad) := by
    apply holds_transport mid out (separator+1) _ (by simpa only [separator] using hbank)
    intro q hq _
    exact (hbankFrame q (by omega)).symm
  refine ⟨dst,next,nextName,a+b,out,hsucc,hnext,by omega,?_,?_,hnextWord,?_,houtleft,?_,?_,?_,?_,?_⟩
  · simp only [gstep]
  · simp only [gstep]
  · rw [gbank]
    have he : separator+1=h+4+(k : Int) := by dsimp [separator]; omega
    simpa only [he,List.append_assoc,List.cons_append] using houtbank
  · simpa only [separator] using houtgap
  · simpa only [separator] using houtsep
  · simpa only [separator] using hright
  · intro q hq
    rw [gbank] at hq
    have hlimit : pos+1+((value+(encode (graphTail++more)).length : Nat) : Int)<q := by
      simp only [encode_append,List.length_append,Nat.cast_add] at *
      dsimp [pos,separator] at *
      simp only [encode_append,List.length_append,encode,block_length,Nat.cast_add] at hq
      push_cast at hq
      omega
    have hm : mid q=clearAt h t q := hframe q (by dsimp [pos,separator] at *; omega) (Or.inr hlimit)
    rw [hbankFrame q (by dsimp [pos,separator] at *; omega),hm]
    simp [clearAt,show q≠h by dsimp [pos,separator] at *; omega]
  · exact segAdd machine _ _ _ a b hseg hcarry


#print axioms increment_to_first_successor_frame
end Shared.Beeping.NPcoNP.Grammar284IncrementTailFrame
