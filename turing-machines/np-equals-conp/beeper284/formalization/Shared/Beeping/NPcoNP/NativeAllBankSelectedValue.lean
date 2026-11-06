import Shared.Beeping.NPcoNP.NativeArrayGraphBank
import Shared.Beeping.NPcoNP.NativeAllBankScan

/-! The position selected by a finite physical bank prefix is the matching
producer-array and suffix-indexed graph value, under an explicit bank layout. -/
namespace Shared.Beeping.NPcoNP.NativeAllBankSelectedValue
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Coalescing284Map
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

theorem selected_graph_value (bank : Bank 12) (n : Fin 12)
    (values tail : List Nat) (value : Nat)
    (hlen : values.length=n.val) (layout : arrayBank bank=values++value::tail) :
    value=bank (arrayToSuffix n) := by
  have h := congrArg (fun xs : List Nat => xs[n.val]?) layout
  have hleft : (arrayBank bank)[n.val]? = some (bank (arrayToSuffix n)) := by
    rw [List.getElem?_eq_getElem (by simpa only [arrayBank,List.length_ofFn] using n.isLt)]
    simp only [arrayBank,List.getElem_ofFn]
  have hright : (values++value::tail)[n.val]? = some value := by
    rw [List.getElem?_append_right (by omega)]
    simp [←hlen]
  rw [hleft,hright] at h
  exact (Option.some.inj h).symm

/-- Graph suffix and operation kind named by each ordinary coalesced
increment or decrement leaf. -/
def namedSuffix : String → Option (Fin 12 × Bool)
  | "3.$coalesced.0.decnz" => some (0,false)
  | "3.$coalesced.0.inc" => some (0,true)
  | "3.$coalesced.1.decnz" => some (1,false)
  | "3.$coalesced.1.inc" => some (1,true)
  | "3.$coalesced.2.decnz" => some (2,false)
  | "3.$coalesced.2.inc" => some (2,true)
  | "3.$coalesced.3.decnz" => some (3,false)
  | "3.$coalesced.3.inc" => some (3,true)
  | "3.$coalesced.4.decnz" => some (4,false)
  | "3.$coalesced.4.inc" => some (4,true)
  | "3.$coalesced.5.decnz" => some (5,false)
  | "3.$coalesced.5.inc" => some (5,true)
  | "3.$coalesced.6.decnz" => some (6,false)
  | "3.$coalesced.6.inc" => some (6,true)
  | "3.$coalesced.7.decnz" => some (7,false)
  | "3.$coalesced.7.inc" => some (7,true)
  | "3.$coalesced.8.decnz" => some (8,false)
  | "3.$coalesced.8.inc" => some (8,true)
  | "3.$coalesced.9.decnz" => some (9,false)
  | "3.$coalesced.9.inc" => some (9,true)
  | "3.$coalesced.10.decnz" => some (10,false)
  | "3.$coalesced.10.inc" => some (10,true)
  | "3.$coalesced.11.decnz" => some (11,false)
  | "3.$coalesced.11.inc" => some (11,true)
  | _ => none

def namedSuffixOK (entry : Path × String) : Bool :=
  namedSuffix entry.2 == (namedOperation entry.2).map (fun p => (arrayToSuffix p.1,p.2))

/-- The physical position map matches the producer-array to suffix conversion
for every expanded leaf. -/
theorem all_named_suffixes_checked :
    traceState557.acc.leaves.toList.all namedSuffixOK = true := by
  decide

theorem named_position_suffix (entry : Path × String)
    (member : entry ∈ traceState557.acc.leaves.toList) (n : Fin 12) (increment : Bool)
    (operation : namedOperation entry.2=some (n,increment)) :
    namedSuffix entry.2=some (arrayToSuffix n,increment) := by
  have h := List.all_eq_true.mp all_named_suffixes_checked entry member
  simpa only [namedSuffixOK,operation,Option.map_some,beq_iff_eq] using h

/-- For a named operation and an explicitly matched bank layout, the touched
physical value is exactly the named graph suffix value. -/
theorem named_selected_graph_value (entry : Path × String)
    (member : entry ∈ traceState557.acc.leaves.toList) (n : Fin 12) (increment : Bool)
    (operation : namedOperation entry.2=some (n,increment))
    (bank : Bank 12) (values tail : List Nat) (value : Nat)
    (hlen : values.length=n.val) (layout : arrayBank bank=values++value::tail) :
    namedSuffix entry.2=some (arrayToSuffix n,increment) ∧
      value=bank (arrayToSuffix n) :=
  ⟨named_position_suffix entry member n increment operation,
    selected_graph_value bank n values tail value hlen layout⟩

#print axioms selected_graph_value
#print axioms all_named_suffixes_checked
#print axioms named_position_suffix
#print axioms named_selected_graph_value
end Shared.Beeping.NPcoNP.NativeAllBankSelectedValue
