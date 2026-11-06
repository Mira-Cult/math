import Shared.Beeping.NPcoNP.Grammar284PaddedIncrement
import Shared.Beeping.NPcoNP.Grammar284PaddedPositive
import Shared.Beeping.NPcoNP.Grammar284PreparedOrdinaryStep
import Shared.Beeping.NPcoNP.NativeIncSelected

/-! A finite reserve is consumed at most one cell per ordinary graph step.
Special operations and an unbounded blank-tail invariant are separate. -/
namespace Shared.Beeping.NPcoNP.Grammar284OrdinaryWindow
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeIncSelected
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284ExpansionPaths
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.Grammar284PaddedIncrement
open Shared.Beeping.NPcoNP.Grammar284PaddedPositive
open Shared.Beeping.NPcoNP.Grammar284PreparedOrdinaryStep
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

/-- A graph state and literal tape agree at a parser boundary with a finite
reserve of at least `reserve+2` blank cells after the unary bank. -/
def Window (state : Fin 185) (bank : Bank 12) (origin separator : Int)
    (t : Int → Bool) (reserve : Nat) : Prop :=
  ∃ (path : Path) (name : String) (more : List Nat),
    graphLeaf state=some (path,name) ∧ origin+59≤separator ∧ Holds t origin path ∧
    (∀ q, q<origin → t q=false) ∧
    (∀ q, origin+((path.length : Nat) : Int)-1<q → q<separator-1 → t q=false) ∧
    t (separator-1)=true ∧ t separator=false ∧
    Holds t (separator+1) (encode (arrayBank bank++more) ++ List.replicate (reserve+2) false)

/-- A non-root named increment or decrement silently advances the graph and
preserves a window, consuming at most one reserved blank cell. -/
theorem ordinary_step (state : Fin 185) (graph : Bank 12) (origin separator : Int)
    (t : Int → Bool) (reserve : Nat) (window : Window state graph origin separator t (reserve+1))
    (notRoot : state.val≠184)
    (named : ∀ path name, graphLeaf state=some (path,name) →
      ∃ n inc, namedOperation name=some (n,inc)) :
    let result := target.system.step ⟨state,graph⟩
    ∃ steps out, 0<steps ∧ result.2=[] ∧
      Window result.1.state result.1.bank origin separator out reserve ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  dsimp only
  obtain ⟨path,name,more,hleaf,hroom,hword,hleft,hgap,hright,hsep,hbank⟩ := window
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
    cases inc with
    | true =>
      have hinput : Holds t (separator+1)
          ((encode (values++value::(graphTail++more)) ++ [false]) ++ List.replicate (reserve+2) false) := by
        simpa [hlayout,List.replicate_succ,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hbank
      obtain ⟨steps,last,out,hs,hevent,hgraph,hw,hl,hg,hr,hsep',hb,hseg⟩ :=
        increment_step_padded state path name hleaf notRoot n hop graph values graphTail more value
          (List.replicate (reserve+2) false) hlen hlayout origin h separator t rfl space room hword hleft gap hright hsep hinput
      refine ⟨steps,out,hs,hevent,?_,hseg⟩
      exact ⟨last.1,last.2,more,by simpa using hgraph,hroom,hw,hl,hg,hr,hsep',hb⟩
    | false =>
      cases value with
      | zero =>
        have hinput : Holds t (separator+1)
            (encode (arrayBank graph++more) ++ List.replicate ((reserve+1)+2) false) := hbank
        obtain ⟨steps,last,out,hs,hevent,hgraph,hw,hl,hg,hr,hsep',hb,hseg⟩ :=
          zero_step state path name hleaf notRoot n hop graph values graphTail more
            (List.replicate ((reserve+1)+2) false) hlen hlayout origin h separator t rfl space room
            hword hleft gap hright hsep hinput
        have hb' : Holds out (separator+1)
            (encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++more) ++ List.replicate (reserve+2) false) := by
          apply holds_prefix out (separator+1) _ [false]
          simpa [List.replicate_succ',List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb
        refine ⟨steps,out,hs,hevent,?_,hseg⟩
        exact ⟨last.1,last.2,more,by simpa using hgraph,hroom,hw,hl,hg,hr,hsep',hb'⟩
      | succ value =>
        have hinput : Holds t (separator+1)
            ((encode values ++ (encode ((value+1)::(graphTail++more)) ++ [false,false])) ++
              List.replicate (reserve+1) false) := by
          simpa [hlayout,encode_append,encode,List.replicate_succ,List.append_assoc,
            Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hbank
        obtain ⟨steps,last,out,hs,hevent,hgraph,hw,hl,hg,hr,hsep',hb,hseg⟩ :=
          positive_step_padded state path name hleaf notRoot n hop graph values graphTail more value
            (List.replicate (reserve+1) false) hlen hlayout origin h separator t rfl space room
            hword hleft gap hright hsep hinput
        have hb' : Holds out (separator+1)
            (encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++(more++[0])) ++
              List.replicate (reserve+2) false) := by
          simpa [List.replicate_succ,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb
        refine ⟨steps,out,hs,hevent,?_,hseg⟩
        exact ⟨last.1,last.2,more++[0],by simpa using hgraph,hroom,hw,hl,hg,hr,hsep',hb'⟩

#print axioms ordinary_step
end Shared.Beeping.NPcoNP.Grammar284OrdinaryWindow
