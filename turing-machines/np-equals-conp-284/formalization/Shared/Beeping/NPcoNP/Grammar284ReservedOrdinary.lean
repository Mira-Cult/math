import Shared.Beeping.NPcoNP.Grammar284ReservedWindow
import Shared.Beeping.NPcoNP.Grammar284InfiniteWindowBridge
import Shared.Beeping.NPcoNP.Grammar284PaddedPositive
import Shared.Beeping.NPcoNP.Grammar284PreparedOrdinaryStep
import Shared.Beeping.NPcoNP.NativeIncBank

/-! Named non-root ordinary instructions preserve the additional zero-block
reserve as well as the infinite blank tail. -/
namespace Shared.Beeping.NPcoNP.Grammar284ReservedOrdinary
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284ExpansionPaths
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.Grammar284GraphOperation
open Shared.Beeping.NPcoNP.Grammar284BankCorrespondence
open Shared.Beeping.NPcoNP.Grammar284PaddedIncrement
open Shared.Beeping.NPcoNP.Grammar284PaddedPositive
open Shared.Beeping.NPcoNP.Grammar284PreparedOrdinaryStep
open Shared.Beeping.NPcoNP.Grammar284InfiniteWindowBridge
open Shared.Beeping.NPcoNP.Grammar284ReservedWindow
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

theorem ordinary_step (state : Fin 185) (graph : Bank 12) (origin separator : Int)
    (t : Int → Bool) (window : ReservedWindow state graph origin separator t)
    (notRoot : state.val≠184)
    (named : ∀ path name, graphLeaf state=some (path,name) →
      ∃ n inc, namedOperation name=some (n,inc)) :
    let result := target.system.step ⟨state,graph⟩
    ∃ steps out, 0<steps ∧ result.2=[] ∧
      ReservedWindow result.1.state result.1.bank origin separator out ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  dsimp only
  obtain ⟨path,name,more,hleaf,hroom,hword,hleft,hgap,hright,hsep,hbank,htail⟩ := window
  obtain ⟨n,inc,hop⟩ := named path name hleaf
  let arr := arrayBank graph
  have narr : n.val<arr.length := by simp [arr,arrayBank]
  let values := arr.take n.val
  have hlen : values.length=n.val := by simp [values,List.length_take_of_le (by omega : n.val≤arr.length)]
  cases hdrop : arr.drop n.val with
  | nil =>
    have hdlen := congrArg List.length hdrop
    simp only [List.length_drop,List.length_nil] at hdlen
    omega
  | cons value graphTail =>
    have hlayout : arrayBank graph=values++value::graphTail := by
      have he := List.take_append_drop n.val arr
      simpa only [values,hdrop,arr] using he.symm
    have walk : PreparedWalk path (.op name) :=
      expanded_leaf_follows traceState557.acc producerExpand (path,name) (graph_leaf_member state path name hleaf)
    have hlenpath : path.length≤55 := (prepared_path_bound path (.op name) walk).1
    let h := origin+((path.length : Nat) : Int)
    have space : h+4≤separator := by dsimp [h]; omega
    have room : origin+55<separator := by omega
    have gap : ∀ q, h≤q → q<separator-1 → t q=false := by
      intro q hq hq'
      exact hgap q (by dsimp [h] at hq; omega) hq'
    let moreFull := more++[0]
    let old := encode (arrayBank graph++moreFull)
    have hfull : Holds t (separator+1) old := by
      simpa [old,moreFull,encode_append,encode,block,List.append_assoc] using hbank
    have hblank : ∀ q, separator+1+((old.length : Nat) : Int)≤q → t q=false := by
      intro q hq
      apply htail
      have he : old.length=(encode (arrayBank graph++more)).length+2 := by
        simp [old,moreFull,encode_append,encode,block,List.append_assoc,Nat.add_assoc]
      rw [he] at hq
      push_cast at hq
      omega
    have hblank2 : Holds t (separator+1+((old.length : Nat) : Int)) [false,false] := by
      simpa using blank_replicate t (separator+1+((old.length : Nat) : Int)) 2 hblank
    have hpadded : Holds t (separator+1) (old ++ [false,false]) :=
      holds_append_intro t (separator+1) old [false,false] hfull hblank2
    cases inc with
    | true =>
      have hinput : Holds t (separator+1)
          ((encode (values++value::(graphTail++moreFull)) ++ [false]) ++ [false]) := by
        simpa [old,hlayout,List.append_assoc] using hpadded
      obtain ⟨steps,last,out,hs,hevent,hgraph,hw,hl,hg,hr,hsep',hb,hfar,hseg⟩ :=
        increment_step_frame state path name hleaf notRoot n hop graph values graphTail moreFull value [false]
          hlen hlayout origin h separator t rfl space room hword hleft gap hright hsep hinput
      have hresult : Holds out (separator+1)
          (encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++more) ++ [true,false]) := by
        apply Shared.Beeping.NPcoNP.NativeIncSelected.holds_prefix out (separator+1) _ [false]
        simpa [moreFull,encode_append,encode,block,List.append_assoc] using hb
      have gs := graph_increment_step state path name hleaf n hop graph values graphTail value hlen hlayout
      have gbank : arrayBank (target.system.step ⟨state,graph⟩).1.bank=values++(value+1)::graphTail := by
        rw [gs]
        exact write_selected_array graph n values graphTail value (value+1) hlen hlayout
      have hend : ∀ q, separator+1+((encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++more)).length : Int)+2≤q → out q=false := by
        intro q hq
        have hf : separator+1+((encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++moreFull)).length : Int)≤q := by
          have he : (encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++moreFull)).length=
              (encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++more)).length+2 := by
            simp [moreFull,encode_append,encode,block,List.append_assoc,Nat.add_assoc]
          rw [he]; push_cast; omega
        rw [hfar q hf]
        apply htail
        rw [gbank] at hq
        rw [hlayout]
        simp only [encode_append,List.length_append,encode,block_length,Nat.cast_add] at *
        push_cast at *
        omega
      have ht := tail_from_end out (separator+1) _ hresult hend
      refine ⟨steps,out,hs,hevent,?_,hseg⟩
      exact ⟨last.1,last.2,more,by simpa using hgraph,hroom,hw,hl,hg,hr,hsep',hresult,by intro q hq; apply ht; omega⟩
    | false =>
      cases value with
      | zero =>
        obtain ⟨steps,last,out,hs,hevent,hgraph,hw,hl,hg,hr,hsep',hb,hfar,hseg⟩ :=
          zero_step_frame state path name hleaf notRoot n hop graph values graphTail more [true,false]
            hlen hlayout origin h separator t rfl space room hword hleft gap hright hsep hbank
        have gs := graph_decrement_zero_step state path name hleaf n hop graph values graphTail hlen hlayout
        have ht : ∀ q, separator+2+((encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++more)).length : Int)≤q → out q=false := by
          intro q hq
          rw [gs] at hq
          rw [hfar q (by omega)]
          exact htail q hq
        refine ⟨steps,out,hs,hevent,?_,hseg⟩
        exact ⟨last.1,last.2,more,by simpa using hgraph,hroom,hw,hl,hg,hr,hsep',hb,ht⟩
      | succ value =>
        have hinput : Holds t (separator+1)
            ((encode values ++ (encode ((value+1)::(graphTail++moreFull)) ++ [false,false])) ++ []) := by
          simpa [old,hlayout,encode_append,encode,List.append_assoc] using hpadded
        obtain ⟨steps,last,out,hs,hevent,hgraph,hw,hl,hg,hr,hsep',hb,hfar,hseg⟩ :=
          positive_step_frame state path name hleaf notRoot n hop graph values graphTail moreFull value []
            hlen hlayout origin h separator t rfl space room hword hleft gap hright hsep hinput
        let more' := moreFull
        have hresult : Holds out (separator+1)
            (encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++more') ++ [true,false]) := by
          apply Shared.Beeping.NPcoNP.NativeIncSelected.holds_prefix out (separator+1) _ [false]
          simpa [more',encode_append,encode,block,List.append_assoc] using hb
        have gs := graph_decrement_positive_step state path name hleaf n hop graph values graphTail value hlen hlayout
        have gbank : arrayBank (target.system.step ⟨state,graph⟩).1.bank=values++value::graphTail := by
          rw [gs]
          exact write_selected_array graph n values graphTail (value+1) value hlen hlayout
        have hend : ∀ q, separator+1+((encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++more')).length : Int)+2≤q → out q=false := by
          intro q hq
          have hf : separator+1+((encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++moreFull++[0])).length : Int)≤q := by
            have he : (encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++moreFull++[0])).length=
                (encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++more')).length+2 := by
              simp [more',encode_append,encode,block,List.append_assoc,Nat.add_assoc]
            rw [he]; push_cast; omega
          rw [hfar q hf]
          apply htail
          rw [gbank] at hq
          rw [hlayout]
          simp only [more',moreFull,encode_append,List.length_append,encode,block,block_length,Nat.cast_add,List.length_cons,List.length_nil,List.length_replicate] at *
          push_cast at *
          omega
        have ht := tail_from_end out (separator+1) _ hresult hend
        refine ⟨steps,out,hs,hevent,?_,hseg⟩
        exact ⟨last.1,last.2,more',by simpa using hgraph,hroom,hw,hl,hg,hr,hsep',hresult,by intro q hq; apply ht; omega⟩

#print axioms ordinary_step
end Shared.Beeping.NPcoNP.Grammar284ReservedOrdinary
