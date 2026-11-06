import Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch
import Shared.Beeping.NPcoNP.NativeSelectorParserGeneric

/-! Compose the literal selector and grammar dispatch for a supplied prepared
leaf and compatible tape window. Operation and routine effects remain separate. -/
namespace Shared.Beeping.NPcoNP.NativeGrammarSelectorDispatch
open PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeFirstDispatch
open Shared.Beeping.NPcoNP.NativeSelectorParserGeneric
open Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch
open Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284ExpansionPaths
open Shared.Beeping.NPcoNP.Grammar284ForwardParser
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

/-- A supplied prepared word begins with the selector's first true cell; the
rest is exactly the control word seen from state 93. -/
theorem prepared_head_tail (t : Int → Bool) (origin : Int) (path : Path)
    (name : String) (walk : PreparedWalk path (.op name))
    (word : Holds t origin path) :
    t origin=true ∧ Holds t (origin+1) path.tail := by
  obtain ⟨raw,he,_⟩ := walk
  have shape : path=true::path.tail := by rw [he]; rfl
  rw [shape] at word
  exact word

/-- Any ordinary expanded leaf can be selected and dispatched to its exact
literal operation entry, silently and without changing the supplied tape. -/
theorem ordinary_selector_dispatch (e : Expansion)
    (expanded : expand producerGrammar.nodes 53 (.node producerGrammar.root)
      [true,true,false] [] {} = some e)
    (entry : Path × String) (member : entry ∈ e.leaves.toList)
    (q : Fin 284) (target : operationEntry entry.2=some q)
    (t : Int → Bool) (head origin : Int) (ks : List Nat)
    (hlen : ks.length=14) (window : downHolds t head (blocks ks ++ []))
    (horder : head-((blocks ks).length : Int) ≤ origin)
    (left : ∀ p, p<origin → t p=false) (word : Holds t origin entry.1) :
    ∃ k, 0<k ∧ parseForward 52 t origin=some (entry.2,entry.1.length) ∧
      silentSegment machine (cfg 83 head t)
        (cfg q (origin+1+(entry.1.tail.length : Int)) t)
        (k+entry.1.tail.length) := by
  have walk := expanded_leaf_follows e expanded entry member
  obtain ⟨first,tail⟩ := prepared_head_tail t origin entry.1 entry.2 walk word
  obtain ⟨positive,selector,parsed⟩ := selector_to_parser t head origin ks entry.1 entry.2
    hlen window horder left first walk word
  have dispatch := expanded_leaf_dispatch_to_entry e expanded entry member q target (origin+1) t tail
  refine ⟨(blocks ks).length+(origin-(head-((blocks ks).length : Int))).toNat+1,
    positive,parsed,?_⟩
  exact segAdd machine _ _ _ _ _ selector dispatch

/-- Any administrative expanded leaf can be selected and dispatched to its
routine entry, silently erasing only its final control cell along the way. -/
theorem administrative_selector_dispatch (e : Expansion)
    (expanded : expand producerGrammar.nodes 53 (.node producerGrammar.root)
      [true,true,false] [] {} = some e)
    (entry : Path × String) (member : entry ∈ e.leaves.toList)
    (q : Fin 284) (target : administrativeEntry entry.2=some q)
    (t : Int → Bool) (head origin : Int) (ks : List Nat)
    (hlen : ks.length=14) (window : downHolds t head (blocks ks ++ []))
    (horder : head-((blocks ks).length : Int) ≤ origin)
    (left : ∀ p, p<origin → t p=false) (word : Holds t origin entry.1) :
    ∃ k, 0<k ∧ parseForward 52 t origin=some (entry.2,entry.1.length) ∧
      silentSegment machine (cfg 83 head t)
        (cfg q (origin+1+(entry.1.tail.dropLast.length : Int)-1)
          ((cfg (93 : Fin 284) (origin+1+(entry.1.tail.dropLast.length : Int)) t).write false))
        (k+(entry.1.tail.dropLast.length+1)) := by
  have walk := expanded_leaf_follows e expanded entry member
  obtain ⟨first,tail⟩ := prepared_head_tail t origin entry.1 entry.2 walk word
  obtain ⟨positive,selector,parsed⟩ := selector_to_parser t head origin ks entry.1 entry.2
    hlen window horder left first walk word
  have dispatch := expanded_administrative_dispatch e expanded entry member q target (origin+1) t tail
  refine ⟨(blocks ks).length+(origin-(head-((blocks ks).length : Int))).toNat+1,
    positive,parsed,?_⟩
  exact segAdd machine _ _ _ _ _ selector dispatch

/-- For every expanded leaf, selection proceeds to exactly one mapped entry
kind. This classification is finite and makes no reachability assertion. -/
theorem every_leaf_selector_dispatch (e : Expansion)
    (expanded : expand producerGrammar.nodes 53 (.node producerGrammar.root)
      [true,true,false] [] {} = some e)
    (entry : Path × String) (member : entry ∈ e.leaves.toList)
    (t : Int → Bool) (head origin : Int) (ks : List Nat)
    (hlen : ks.length=14) (window : downHolds t head (blocks ks ++ []))
    (horder : head-((blocks ks).length : Int) ≤ origin)
    (left : ∀ p, p<origin → t p=false) (word : Holds t origin entry.1) :
    ∃ k, 0<k ∧ parseForward 52 t origin=some (entry.2,entry.1.length) ∧
      ((∃ q, operationEntry entry.2=some q ∧
        silentSegment machine (cfg 83 head t)
          (cfg q (origin+1+(entry.1.tail.length : Int)) t) (k+entry.1.tail.length)) ∨
       (∃ q, administrativeEntry entry.2=some q ∧
        silentSegment machine (cfg 83 head t)
          (cfg q (origin+1+(entry.1.tail.dropLast.length : Int)-1)
            ((cfg (93 : Fin 284) (origin+1+(entry.1.tail.dropLast.length : Int)) t).write false))
          (k+(entry.1.tail.dropLast.length+1)))) := by
  have listed : entry ∈ Grammar284.ExpandSteps.ProducerTrace.traceState557.acc.leaves.toList := by
    have he := expanded
    rw [Grammar284.ExpandSteps.ProducerTrace.producerExpand] at he
    cases he
    exact member
  have partition := List.all_eq_true.mp all_leaf_entry_maps_partition entry listed
  cases ho : operationEntry entry.2 with
  | some q =>
    obtain ⟨k,hk,hparse,hseg⟩ := ordinary_selector_dispatch e expanded entry member q ho
      t head origin ks hlen window horder left word
    exact ⟨k,hk,hparse,Or.inl ⟨q,rfl,hseg⟩⟩
  | none =>
    cases ha : administrativeEntry entry.2 with
    | none => simp [ho,ha] at partition
    | some q =>
      obtain ⟨k,hk,hparse,hseg⟩ := administrative_selector_dispatch e expanded entry member q ha
        t head origin ks hlen window horder left word
      exact ⟨k,hk,hparse,Or.inr ⟨q,rfl,hseg⟩⟩

#print axioms every_leaf_selector_dispatch
#print axioms ordinary_selector_dispatch
#print axioms administrative_selector_dispatch
end Shared.Beeping.NPcoNP.NativeGrammarSelectorDispatch
