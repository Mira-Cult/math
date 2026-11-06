import Shared.Beeping.NPcoNP.NativeBankScanGeneric
import Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch

/-! Uniform finite-prefix bank scanning for each of the twelve producer
positions. The supplied physical window and return operation remain separate. -/
namespace Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.Native279BankScan
open Shared.Beeping.NPcoNP.NativeBankScanGeneric
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

/-- Literal scanner state indexed by the number of preceding unary blocks. -/
def scannerStart (n : Fin 12) : Fin 284 :=
  match n.val with
  | 0 => 271
  | 1 => 275
  | 2 => 276
  | 3 => 277
  | 4 => 278
  | 5 => 279
  | 6 => 280
  | 7 => 281
  | 8 => 282
  | 9 => 272
  | 10 => 273
  | _ => 274

/-- The three control scans and the bank-prefix chain cover all twelve
possible numbers of preceding blocks. -/
theorem scanner_paths (n : Fin 12) :
    ∃ q1 q2 q3, RightRow (scannerStart n) q1 ∧ RightRow q1 q2 ∧
      RightRow q2 q3 ∧ Chain n.val q3 42 := by
  fin_cases n <;> simp only [scannerStart]
  · exact ⟨270,9,42,.r271,.r270,.r9,(.refl 42)⟩
  · exact ⟨271,270,9,.r275,.r271,.r270,(.cons .r9 (.refl 42))⟩
  · exact ⟨275,271,270,.r276,.r275,.r271,(.cons .r270 (.cons .r9 (.refl 42)))⟩
  · exact ⟨276,275,271,.r277,.r276,.r275,(.cons .r271 (.cons .r270 (.cons .r9 (.refl 42))))⟩
  · exact ⟨277,276,275,.r278,.r277,.r276,(.cons .r275 (.cons .r271 (.cons .r270 (.cons .r9 (.refl 42)))))⟩
  · exact ⟨278,277,276,.r279,.r278,.r277,(.cons .r276 (.cons .r275 (.cons .r271 (.cons .r270 (.cons .r9 (.refl 42))))))⟩
  · exact ⟨279,278,277,.r280,.r279,.r278,(.cons .r277 (.cons .r276 (.cons .r275 (.cons .r271 (.cons .r270 (.cons .r9 (.refl 42)))))))⟩
  · exact ⟨280,279,278,.r281,.r280,.r279,(.cons .r278 (.cons .r277 (.cons .r276 (.cons .r275 (.cons .r271 (.cons .r270 (.cons .r9 (.refl 42))))))))⟩
  · exact ⟨281,280,279,.r282,.r281,.r280,(.cons .r279 (.cons .r278 (.cons .r277 (.cons .r276 (.cons .r275 (.cons .r271 (.cons .r270 (.cons .r9 (.refl 42)))))))))⟩
  · exact ⟨282,281,280,.r272,.r282,.r281,(.cons .r280 (.cons .r279 (.cons .r278 (.cons .r277 (.cons .r276 (.cons .r275 (.cons .r271 (.cons .r270 (.cons .r9 (.refl 42))))))))))⟩
  · exact ⟨272,282,281,.r273,.r272,.r282,(.cons .r281 (.cons .r280 (.cons .r279 (.cons .r278 (.cons .r277 (.cons .r276 (.cons .r275 (.cons .r271 (.cons .r270 (.cons .r9 (.refl 42)))))))))))⟩
  · exact ⟨273,272,282,.r274,.r273,.r272,(.cons .r282 (.cons .r281 (.cons .r280 (.cons .r279 (.cons .r278 (.cons .r277 (.cons .r276 (.cons .r275 (.cons .r271 (.cons .r270 (.cons .r9 (.refl 42))))))))))))⟩

/-- For any physical bank position, a compatible control window and finite
unary bank prefix lead silently to state 262 after clearing the first cell of
the target block. The arbitrary target value and remaining tail are preserved
outside that one cell. -/
theorem scan_all_positions (n : Fin 12) (h : Int) (t : Int → Bool) (k : Nat)
    (values : List Nat) (value : Nat) (tail : List Bool)
    (hlen : values.length=n.val) (h0 : t h=false) (h1 : t (h+1)=false)
    (control : ∀ i : Nat, i<k → t (h+2+(i : Int))=true)
    (delimiter : t (h+2+(k : Int))=false)
    (bank : Holds t (h+3+(k : Int)) (encode values ++ (block value ++ tail))) :
    let pos := h+3+(k : Int)+((encode values).length : Int)
    (∀ q, q≠pos → clearAt pos t q=t q) ∧
    silentSegment machine (cfg (scannerStart n) h t) (cfg 262 (pos-2) (clearAt pos t))
      (k+(encode values).length+5) := by
  obtain ⟨q1,q2,q3,r0,r1,r2,chain⟩ := scanner_paths n
  exact scan_to262 r0 r1 r2 chain h t k values value tail hlen h0 h1 control delimiter bank

/-- Entry state for a decrement or increment at the given physical bank
position. `increment=true` selects the increment row. -/
def operationAt (n : Fin 12) (increment : Bool) : Fin 284 :=
  let base : Nat := match n.val with
    | 0 => 72 | 1 => 50 | 2 => 52 | 3 => 58 | 4 => 60 | 5 => 62
    | 6 => 64 | 7 => 66 | 8 => 68 | 9 => 70 | 10 => 54 | _ => 56
  ⟨base + if increment then 1 else 0, by
    fin_cases n <;> cases increment <;> decide⟩

/-- All 24 entry rows lead to their position's scanner on a true marker. -/
theorem operation_entry_row (n : Fin 12) (increment : Bool) :
    machine.table.row (operationAt n increment) true =
      ⟨!increment,.right,scannerStart n,false⟩ := by
  fin_cases n <;> cases increment <;> decide

/-- The entry transition and the complete prefix scan compose for every
physical bank position and either operation entry. The scan-window hypotheses
refer to the tape immediately after the entry transition. -/
theorem entry_scan_all_positions (n : Fin 12) (increment : Bool)
    (h : Int) (t : Int → Bool) (k : Nat)
    (values : List Nat) (value : Nat) (tail : List Bool)
    (marker : t h=true) (hlen : values.length=n.val)
    (h0 : (cfg (operationAt n increment) h t).write (!increment) (h+1)=false)
    (h1 : (cfg (operationAt n increment) h t).write (!increment) (h+1+1)=false)
    (control : ∀ i : Nat, i<k →
      (cfg (operationAt n increment) h t).write (!increment) (h+1+2+(i : Int))=true)
    (delimiter : (cfg (operationAt n increment) h t).write (!increment) (h+1+2+(k : Int))=false)
    (bank : Holds ((cfg (operationAt n increment) h t).write (!increment)) (h+1+3+(k : Int))
      (encode values ++ (block value ++ tail))) :
    let u := (cfg (operationAt n increment) h t).write (!increment)
    let pos := h+1+3+(k : Int)+((encode values).length : Int)
    silentSegment machine (cfg (operationAt n increment) h t) (cfg 262 (pos-2) (clearAt pos u))
      (1+(k+(encode values).length+5)) := by
  dsimp only
  have step : machine.step (cfg (operationAt n increment) h t) =
      (cfg (scannerStart n) (h+1) ((cfg (operationAt n increment) h t).write (!increment)),false) := by
    dsimp only [Machine.step,cfg]
    rw [marker,operation_entry_row]
    rfl
  have scan := (scan_all_positions n (h+1) ((cfg (operationAt n increment) h t).write (!increment))
    k values value tail hlen h0 h1 control delimiter bank).2
  exact segAdd machine _ _ _ 1 _ (oneSeg machine _ _ step) scan

/-- Physical bank position and operation kind for each named ordinary
increment or decrement in the producer grammar. -/
def namedOperation : String → Option (Fin 12 × Bool)
  | "3.$coalesced.0.decnz" => some (1,false)
  | "3.$coalesced.0.inc" => some (1,true)
  | "3.$coalesced.1.decnz" => some (2,false)
  | "3.$coalesced.1.inc" => some (2,true)
  | "3.$coalesced.2.decnz" => some (3,false)
  | "3.$coalesced.2.inc" => some (3,true)
  | "3.$coalesced.3.decnz" => some (4,false)
  | "3.$coalesced.3.inc" => some (4,true)
  | "3.$coalesced.4.decnz" => some (5,false)
  | "3.$coalesced.4.inc" => some (5,true)
  | "3.$coalesced.5.decnz" => some (6,false)
  | "3.$coalesced.5.inc" => some (6,true)
  | "3.$coalesced.6.decnz" => some (7,false)
  | "3.$coalesced.6.inc" => some (7,true)
  | "3.$coalesced.7.decnz" => some (8,false)
  | "3.$coalesced.7.inc" => some (8,true)
  | "3.$coalesced.8.decnz" => some (9,false)
  | "3.$coalesced.8.inc" => some (9,true)
  | "3.$coalesced.9.decnz" => some (0,false)
  | "3.$coalesced.9.inc" => some (0,true)
  | "3.$coalesced.10.decnz" => some (10,false)
  | "3.$coalesced.10.inc" => some (10,true)
  | "3.$coalesced.11.decnz" => some (11,false)
  | "3.$coalesced.11.inc" => some (11,true)
  | _ => none

def namedOperationOK (entry : Path × String) : Bool :=
  match namedOperation entry.2 with
  | none => true
  | some (n,increment) => operationEntry entry.2 == some (operationAt n increment)

/-- Every listed named increment and decrement has the expected physical
entry state for its bank position. Half operations and beep are separate. -/
theorem all_named_operations_checked :
    traceState557.acc.leaves.toList.all namedOperationOK = true := by
  decide

theorem named_operation_entry (entry : Path × String)
    (member : entry ∈ traceState557.acc.leaves.toList) (n : Fin 12) (increment : Bool)
    (operation : namedOperation entry.2=some (n,increment)) :
    operationEntry entry.2=some (operationAt n increment) := by
  have h := List.all_eq_true.mp all_named_operations_checked entry member
  simpa only [namedOperationOK,operation,beq_iff_eq] using h

#print axioms scanner_paths
#print axioms scan_all_positions
#print axioms operation_entry_row
#print axioms entry_scan_all_positions
#print axioms all_named_operations_checked
#print axioms named_operation_entry
end Shared.Beeping.NPcoNP.NativeAllBankScan
