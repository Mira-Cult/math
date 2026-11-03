import Shared.PNP.Record285.GrammarCoreZeroDomain

/-! Executable certificate checks for the three-category register invariant. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarCoreZero
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarCoreGraph

def slot (mask : Array Nat) (i : Nat) : Nat := (mask[i]?).getD 0

def subset (a b : Nat) : Bool :=
  (List.range 3).all fun n => !admits a n || admits b n

def otherSlots (before after : Array Nat) (except : Nat) : Bool :=
  (List.range 15).all fun i => if i = except then true else subset (slot before i) (slot after i)

def branchCheck (e : Edge) (i : Nat) (before after : Array Nat) (branch : Bool) : Bool :=
  let others := otherSlots before after i
  (List.range 6).all fun n =>
    if admits (slot before i) n && (operationBranch e n == branch) then
      admits (slot after i) (operationValue e n) && others
    else true

def transfers (spec : CoreRow) (before no yes : Array Nat) : Bool :=
  match operationIndex spec.edge with
  | some i =>
    decide (i < 15) && branchCheck spec.edge i before no false &&
      branchCheck spec.edge i before yes true
  | none => if spec.edge = .beep then otherSlots before no 15 else false

def rowCheck (rows : Array CoreRow) (masks : Array (Array Nat)) (i : Nat) : Bool :=
  match rows[i]?, masks[i]? with
  | some row, some before =>
    match masks[row.no]?, masks[row.yes]? with
    | some no, some yes => transfers row before no yes
    | _, _ => false
  | _, _ => false

def check (rows : Array CoreRow) (masks : Array (Array Nat)) : Bool :=
  decide (rows.size = masks.size) &&
    (List.range masks.size).all (fun i => decide ((masks[i]?.getD #[]).size = 15)) &&
    (List.range 15).all (fun i => admits (slot (masks[0]?.getD #[]) i) 0) &&
    (List.range rows.size).all (rowCheck rows masks)

def selectedZero (rows : Array CoreRow) (masks : Array (Array Nat)) (i : Nat) : Bool :=
  match rows[i]?, masks[i]? with
  | some ⟨.dec reg,_,_⟩, some mask => decide (reg < 15 ∧ slot mask reg = 1)
  | _, _ => false

end Shared.PNP.Record285.GrammarCoreZero
