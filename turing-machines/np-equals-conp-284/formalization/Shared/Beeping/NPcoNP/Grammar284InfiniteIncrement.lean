import Shared.Beeping.NPcoNP.Grammar284OrdinaryWindow
import Shared.Beeping.NPcoNP.NativeIncBank

/-! An infinite blank-tail parser window is preserved by a named non-root
increment. Decrements, HALF, beep, root and reachable initialization are
separate obligations. -/
namespace Shared.Beeping.NPcoNP.Grammar284InfiniteIncrement
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284ExpansionPaths
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.Grammar284PaddedIncrement
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

/-- A parser window with an encoded finite bank followed by an entirely blank
right tail. `more` records the physical reserve blocks outside the graph bank. -/
def InfiniteWindow (state : Fin 185) (bank : Bank 12) (origin separator : Int)
    (t : Int → Bool) : Prop :=
  ∃ (path : Path) (name : String) (more : List Nat),
    graphLeaf state=some (path,name) ∧ origin+59≤separator ∧ Holds t origin path ∧
    (∀ q, q<origin → t q=false) ∧
    (∀ q, origin+((path.length : Nat) : Int)-1<q → q<separator-1 → t q=false) ∧
    t (separator-1)=true ∧ t separator=false ∧
    Holds t (separator+1) (encode (arrayBank bank++more)) ∧
    (∀ q, separator+1+((encode (arrayBank bank++more)).length : Int)≤q → t q=false)

/-- A named increment preserves the infinite-tail window and silently matches
one graph step, provided a sufficiently spaced non-root window is supplied. -/
theorem increment_step (state : Fin 185) (graph : Bank 12) (origin separator : Int)
    (t : Int → Bool) (window : InfiniteWindow state graph origin separator t)
    (notRoot : state.val≠184) (n : Fin 12)
    (named : ∀ path name, graphLeaf state=some (path,name) → namedOperation name=some (n,true)) :
    let result := target.system.step ⟨state,graph⟩
    ∃ steps out, 0<steps ∧ result.2=[] ∧
      InfiniteWindow result.1.state result.1.bank origin separator out ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  dsimp only
  obtain ⟨path,name,more,hleaf,hroom,hword,hleft,hgap,hright,hsep,hbank,htail⟩ := window
  have hop := named path name hleaf
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
    let old := encode (arrayBank graph++more)
    have hb : Holds t (separator+1) old := hbank
    have hz : Holds t (separator+1+(old.length : Int)) [false] := by
      simp only [Holds, and_true]
      exact htail _ (by dsimp [old]; omega)
    have hinput : Holds t (separator+1)
        ((encode (values++value::(graphTail++more)) ++ [false]) ++ []) := by
      have hh := holds_append_intro t (separator+1) old [false] hb hz
      simpa [old,hlayout,List.append_assoc] using hh
    obtain ⟨steps,last,out,hs,hevent,hgraph,hw,hl,hg,hr,hsep',hb',hfar,hseg⟩ :=
      increment_step_frame state path name hleaf notRoot n hop graph values graphTail more value []
        hlen hlayout origin h separator t rfl space room hword hleft gap hright hsep hinput
    have hnewtail : ∀ q, separator+1+((encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++more)).length : Int)≤q → out q=false := by
      intro q hq
      rw [hfar q hq]
      apply htail
      have heq : arrayBank (target.system.step ⟨state,graph⟩).1.bank=values++(value+1)::graphTail := by
        have gs := Shared.Beeping.NPcoNP.Grammar284GraphOperation.graph_increment_step state path name hleaf n hop graph values graphTail value hlen hlayout
        rw [gs]
        exact Shared.Beeping.NPcoNP.Grammar284BankCorrespondence.write_selected_array graph n values graphTail value (value+1) hlen hlayout
      rw [heq] at hq
      rw [hlayout]
      simp only [encode_append,List.length_append,encode,Shared.Beeping.NPcoNP.UnaryBank.block_length,Nat.cast_add] at *
      push_cast at *
      omega
    refine ⟨steps,out,hs,hevent,?_,hseg⟩
    refine ⟨last.1,last.2,more,by simpa using hgraph,hroom,hw,hl,hg,hr,hsep',?_,hnewtail⟩
    simpa using hb'

#print axioms increment_step
end Shared.Beeping.NPcoNP.Grammar284InfiniteIncrement
