import Shared.Beeping.NPcoNP.Grammar284RootReady
import Shared.Beeping.NPcoNP.Grammar284ReservedOrdinary
import Shared.Beeping.NPcoNP.NativeCarryPivot
import Shared.Beeping.NPcoNP.NativeAllBankIncrementPadding
import Shared.Beeping.NPcoNP.NativeGrammarSelectorDispatch

/-! The root increment reaches the distinct `111` parser boundary silently,
matching the graph bank update. Its subsequent beep is separate. -/
namespace Shared.Beeping.NPcoNP.Grammar284RootStep
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeIncSelected
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.NativeAllBankIncrementPadding
open Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch
open Shared.Beeping.NPcoNP.NativeGrammarSelectorDispatch
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.NativeCarryPivot
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284ExpansionPaths
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.Grammar284GraphOperation
open Shared.Beeping.NPcoNP.Grammar284BankCorrespondence
open Shared.Beeping.NPcoNP.Grammar284OrdinaryPreparation
open Shared.Beeping.NPcoNP.Grammar284InfiniteWindowBridge
open Shared.Beeping.NPcoNP.Grammar284ReservedWindow
open Shared.Beeping.NPcoNP.Grammar284RootReady
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 30000000

def rootPath : Path := [true,true,false,true,true,true]
theorem root_leaf : graphLeaf (184 : Fin 185)=some (rootPath,"3.$coalesced.3.inc") := by decide
theorem root_next : target.code[184].yes=0 := by decide
theorem root_operation : namedOperation "3.$coalesced.3.inc"=some (4,true) := by decide

theorem root_step (graph : Bank 12) (origin separator : Int) (t : Int → Bool)
    (window : ReservedWindow 184 graph origin separator t) :
    ∃ steps out, 0<steps ∧ (target.system.step ⟨184,graph⟩).2=[] ∧
      (target.system.step ⟨184,graph⟩).1.state=0 ∧
      RootReady (target.system.step ⟨184,graph⟩).1.bank origin separator out ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  obtain ⟨path,name,more,hleaf,room,word,left,gap,right,sep,bank,tail⟩ := window
  have he : (path,name)=(rootPath,"3.$coalesced.3.inc") := Option.some.inj (hleaf.symm.trans root_leaf)
  cases Prod.mk.inj he with
  | intro hp hn =>
    subst path
    subst name
    let values := (arrayBank graph).take 4
    have hlen : values.length=4 := by simp [values,arrayBank]
    cases hdrop : (arrayBank graph).drop 4 with
    | nil =>
      have hh := congrArg List.length hdrop
      simp [arrayBank] at hh
    | cons value rest =>
      have layout : arrayBank graph=values++value::rest := by
        have hh := List.take_append_drop 4 (arrayBank graph)
        simpa only [values,hdrop] using hh.symm
      let h := origin+6
      have space : h+4≤separator := by dsimp [h]; omega
      have hentry : h=origin+((rootPath.length : Nat) : Int) := by simp [h,rootPath]
      have hgap : ∀ q, h≤q → q<separator-1 → t q=false := by
        intro q hq hq'
        exact gap q (by simp [rootPath] at *; omega) hq'
      obtain ⟨a,mid,ha,hw,hl,hm,hz1,hz2,hcontrol,hsep,hprepFrame,hprep⟩ :=
        prepare_from_parser 184 rootPath _ root_leaf 4 true root_operation origin h separator t
          hentry space word left hgap right sep
      let k := (separator-h-3).toNat
      have hk : (k : Int)=separator-h-3 := Int.toNat_of_nonneg (by omega)
      have hpos : 0<k := by omega
      have hsepEq : h+3+(k : Int)=separator := by omega
      let moreFull := more++[0]
      let old := encode (arrayBank graph++moreFull)
      have hfull : Holds t (separator+1) old := by
        simpa [old,moreFull,encode_append,encode,block,List.append_assoc] using bank
      have hblank : ∀ q, separator+1+((old.length : Nat) : Int)≤q → t q=false := by
        intro q hq
        apply tail
        have he : old.length=(encode (arrayBank graph++more)).length+2 := by
          simp [old,moreFull,encode_append,encode,block,List.append_assoc,Nat.add_assoc]
        rw [he] at hq
        push_cast at hq
        omega
      have hblankWord : Holds t (separator+1+((old.length : Nat) : Int)) [false] := by
        simpa using blank_replicate t _ 1 hblank
      have hpadded : Holds t (separator+1) (old ++ [false]) := holds_append_intro t (separator+1) old [false] hfull hblankWord
      have hbank : Holds mid (h+4+(k : Int))
          ((encode (values++value::(rest++moreFull)) ++ [false]) ++ []) := by
        have hh : Holds mid (separator+1) (old ++ [false]) := by
          apply holds_transport t mid (separator+1) _ hpadded
          intro q hq _
          exact (hprepFrame q (by omega)).symm
        have he : h+4+(k : Int)=separator+1 := by omega
        simpa [he,old,layout,List.append_assoc] using hh
      have hcontrol' : ∀ i : Nat, i<k → mid (h+3+(i : Int))=true := by
        intro i hi
        exact hcontrol _ (by omega) (by omega)
      have member := graph_leaf_member (184 : Fin 185) rootPath "3.$coalesced.3.inc" root_leaf
      have walk : PreparedWalk rootPath (.op "3.$coalesced.3.inc") :=
        expanded_leaf_follows traceState557.acc producerExpand (rootPath,"3.$coalesced.3.inc") member
      obtain ⟨_,hpathTail⟩ := prepared_head_tail mid origin rootPath _ walk hw
      have htarget := named_operation_entry (rootPath,"3.$coalesced.3.inc") member 4 true root_operation
      have hdispatch := expanded_leaf_dispatch_to_entry traceState557.acc producerExpand (rootPath,"3.$coalesced.3.inc") member
        (operationAt 4 true) htarget (origin+1) mid hpathTail
      have hdispatch' : silentSegment machine (cfg 93 (origin+1) mid) (cfg (operationAt 4 true) h mid) rootPath.tail.length := by
        simpa [rootPath,h,show origin+1+5=origin+6 by omega] using hdispatch
      obtain ⟨b,mid2,hb,houtbank,hzero,hzero1,hmark,hones,hsep',hframe,hoperation⟩ :=
        increment_to1_padded 4 h mid k values value (rest++moreFull) [] hm hlen hpos hz1 hz2 hcontrol'
          (by simpa only [hsepEq] using hsep) hbank
      let pos := separator+1+((encode values).length : Int)
      have hmidword : Holds mid2 origin rootPath := by
        apply holds_transport mid mid2 origin rootPath hw
        intro q hq hq'
        have hh := hframe q (by dsimp [h]; omega) (Or.inl (by dsimp [pos,h] at *; omega))
        rw [hh]
        simp [clearAt,show q≠h by dsimp [h] at *; omega]
      have hmidleft : ∀ q, q<origin → mid2 q=false := by
        intro q hq
        have hh := hframe q (by dsimp [h]; omega) (Or.inl (by dsimp [pos,h] at *; omega))
        rw [hh]
        simpa [clearAt,show q≠h by dsimp [h]; omega] using hl q hq
      have hfirst : mid2 origin=true := by
        have hh := hmidword
        simpa [rootPath,Holds] using hh.1
      have hanchor : mid2 (origin+2)=false := by
        have hh := hmidword
        simp only [rootPath,Holds] at hh
        simpa only [show origin+1+1=origin+2 by omega] using hh.2.2.1
      have hbetween : ∀ q, h-1<q → q<h+2 → mid2 q=false := by
        intro q hq hq'
        have he : q=h ∨ q=h+1 := by omega
        rcases he with rfl | rfl
        · exact hzero
        · exact hzero1
      have hmark' : mid2 (h+2)=true := hmark
      have hones' : ∀ q, h+2<q → q<separator → mid2 q=true := by
        intro q hq hq'
        apply hones q (by omega)
        simpa only [hsepEq] using hq'
      have hsep'' : mid2 separator=false := by simpa only [hsepEq] using hsep'
      have hsuffix : ∀ j, 2<j → j<rootPath.length → rootPath[j]?=some true := by
        intro j hj hj'
        have hjcases : j=3 ∨ j=4 ∨ j=5 := by simp [rootPath] at hj'; omega
        rcases hjcases with rfl | rfl | rfl <;> decide
      obtain ⟨c,out,hc,hout,houtleft,houtgap,houtsep,houtmark,hcarryFrame,hcarry⟩ :=
        carry_produces_candidate_exact mid2 origin (h-1) (h+2) separator rootPath rootReadyPath 0 2 0
          (by decide) (by simp [h,rootPath]) (by decide) (by decide) (by decide)
          hsuffix
          (by decide) (by simp [rootReadyPath]; omega) (by decide) hmidword hfirst hanchor hmidleft
          (by omega) hmark' hbetween (by omega) hones' hsep''
      have gstep := graph_increment_step 184 rootPath _ root_leaf 4 root_operation graph values rest value (by simpa using hlen) layout
      have gbank : arrayBank (target.system.step ⟨184,graph⟩).1.bank=values++(value+1)::rest := by
        rw [gstep]
        exact write_selected_array graph 4 values rest value (value+1) (by simpa using hlen) layout
      have hstate : (target.system.step ⟨184,graph⟩).1.state=0 := by
        rw [gstep]
        change target.code[184].yes=0
        exact root_next
      have hbank2 : Holds mid2 (separator+1) (encode (arrayBank (target.system.step ⟨184,graph⟩).1.bank++moreFull)) := by
        rw [gbank]
        simpa [hsepEq,List.append_assoc] using houtbank
      have hbankOutFull : Holds out (separator+1) (encode (arrayBank (target.system.step ⟨184,graph⟩).1.bank++moreFull)) := by
        apply holds_transport mid2 out (separator+1) _ hbank2
        intro q hq _
        exact (hcarryFrame q (by omega)).symm
      have hbankOut : Holds out (separator+1)
          (encode (arrayBank (target.system.step ⟨184,graph⟩).1.bank++more) ++ [true,false]) := by
        simpa [moreFull,encode_append,encode,block,List.append_assoc] using hbankOutFull
      have hend : ∀ q, separator+1+((encode (arrayBank (target.system.step ⟨184,graph⟩).1.bank++more)).length : Int)+2≤q → out q=false := by
        intro q hq
        rw [hcarryFrame q (by omega)]
        have hlimit : pos+1+((value+(encode (rest++moreFull)).length : Nat) : Int)<q := by
          rw [gbank] at hq
          dsimp [pos,moreFull]
          simp only [encode_append,List.length_append,Nat.cast_add] at *
          simp only [moreFull,encode_append,List.length_append,encode,block_length,Nat.cast_add] at hq
          have hz : (encode [0]).length=2 := by decide
          simp only [hz] at *
          push_cast at *
          omega
        have hlimit' : h+3+(k:Int)+1+((encode values).length:Int)+1+((value+(encode (rest++moreFull)).length:Nat):Int)<q := by
          rw [hsepEq]
          exact hlimit
        have hf := hframe q (by dsimp [h]; omega) (Or.inr hlimit')
        rw [hf]
        have hqsep : separator≤q := by omega
        have hmideq := hprepFrame q hqsep
        simp [clearAt,show q≠h by dsimp [h]; omega,hmideq]
        apply tail
        rw [gbank] at hq
        rw [layout]
        simp only [encode_append,List.length_append,encode,block_length,Nat.cast_add] at *
        push_cast at *
        omega
      have htail := tail_from_end out (separator+1) _ hbankOut hend
      have hready : RootReady (target.system.step ⟨184,graph⟩).1.bank origin separator out := by
        refine ⟨more,room,hout,houtleft,?_,houtmark,houtsep,hbankOut,?_⟩
        · intro q hq hq'
          apply houtgap q
          · simp [rootReadyPath]; omega
          · exact hq'
        · intro q hq
          apply htail
          omega
      have hfirstseg := segAdd machine _ _ _ a rootPath.tail.length hprep hdispatch'
      have hsecondseg := segAdd machine _ _ _ _ b hfirstseg hoperation
      refine ⟨a+rootPath.tail.length+b+c,out,by omega,?_,hstate,hready,segAdd machine _ _ _ _ c hsecondseg hcarry⟩
      rw [gstep]

#print axioms root_step
end Shared.Beeping.NPcoNP.Grammar284RootStep
