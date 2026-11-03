import Shared.PNP.Record285.OwnershipCore

/-! Finite checks for the logical mask invariant and the ownership-to-class
control-flow correspondence. The soundness proofs are separate. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.OwnershipCore
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarCoreGraph
open Shared.PNP.Record285.GrammarCoreZero

def singleEdge : Action → Option Edge
  | .inc i => some (.inc i)
  | .dec i => some (.dec i)
  | .half i => some (.half i)
  | _ => none

def others (before after : Array Nat) (first second : Nat) : Bool :=
  (List.range 18).all fun i =>
    if i = first ∨ i = second then true else subset (slot before i) (slot after i)

def singleBranch (e : Edge) (i : Nat) (before after : Array Nat) (branch : Bool) : Bool :=
  let unchanged := others before after i i
  (List.range 6).all fun n =>
    if admits (slot before i) n && (operationBranch e n == branch) then
      admits (slot after i) (operationValue e n) && unchanged
    else true

def moveTransfer (src dst : Nat) (before after : Array Nat) : Bool :=
  decide (src < 18 ∧ dst < 18 ∧ src ≠ dst) &&
  admits (slot after src) 0 && others before after src dst &&
  (List.range 3).all fun a => (List.range 3).all fun b =>
    if admits (slot before src) a && admits (slot before dst) b then
      admits (slot after dst) (a+b)
    else true

def transfer (row : Row) (before no yes : Array Nat) : Bool :=
  match row.action with
  | .inc i => decide (i < 18) && singleBranch (.inc i) i before no false &&
      singleBranch (.inc i) i before yes true
  | .dec i => decide (i < 18) && singleBranch (.dec i) i before no false &&
      singleBranch (.dec i) i before yes true
  | .half i => decide (i < 18) && singleBranch (.half i) i before no false &&
      singleBranch (.half i) i before yes true
  | .move src dst => moveTransfer src dst before no
  | .beep => others before no 18 18

def invariantRow (rows : Array Row) (masks : Array (Array Nat)) (i : Nat) : Bool :=
  match rows[i]?, masks[i]? with
  | some row, some before =>
    match masks[row.no]?, masks[row.yes]? with
    | some no, some yes => transfer row before no yes
    | _, _ => false
  | _, _ => false

def invariantCheck (rows : Array Row) (masks : Array (Array Nat)) : Bool :=
  decide (rows.size = masks.size) &&
  (List.range masks.size).all (fun i => decide ((masks[i]?.getD #[]).size = 18)) &&
  (List.range 18).all (fun i => admits (slot (masks[0]?.getD #[]) i) 0) &&
  (List.range rows.size).all (invariantRow rows masks)

def classAt (classes : Array Nat) (i : Nat) : Nat := (classes[i]?).getD 15

def peerZero (classes mask : Array Nat) (i : Nat) : Bool :=
  (List.range 18).all fun j =>
    if j ≠ i ∧ classAt classes j = classAt classes i then decide (slot mask j = 1) else true

def targetEdge (classes : Array Nat) : Action → Edge
  | .inc i => .inc (classAt classes i)
  | .dec i => .dec (classAt classes i)
  | .half i => .half (classAt classes i)
  | .move src _ => .dec (classAt classes src)
  | .beep => .beep

def mappingRow (logical : Array Row) (physical : Array CoreRow) (masks : Array (Array Nat))
    (classes mapping : Array Nat) (i : Nat) : Bool :=
  match logical[i]?, masks[i]?, mapping[i]? with
  | some row, some mask, some pc =>
    match physical[pc]?, mapping[row.no]?, mapping[row.yes]? with
    | some target, some no, some yes =>
      let same := decide (target.edge = targetEdge classes row.action)
      match row.action with
      | .inc reg | .dec reg | .half reg =>
        same && peerZero classes mask reg && decide (target.no = no ∧ target.yes = yes)
      | .beep => same && decide (target.no = no ∧ target.yes = yes)
      | .move src dst =>
        match physical[target.no]? with
        | none => false
        | some body =>
          same && peerZero classes mask src && peerZero classes mask dst &&
            decide (classAt classes src ≠ classAt classes dst) &&
            decide (body.edge = .inc (classAt classes dst) ∧ body.no = pc ∧ body.yes = pc ∧
              target.yes = no ∧ row.no = row.yes)
    | _, _, _ => false
  | _, _, _ => false

def mappingCheck (logical : Array Row) (physical : Array CoreRow) (masks : Array (Array Nat))
    (classes mapping : Array Nat) : Bool :=
  decide (logical.size = mapping.size ∧ classes.size = 18 ∧ mapping[0]? = some 0) &&
  (List.range 18).all (fun i => decide (classAt classes i < 15)) &&
  (List.range logical.size).all (mappingRow logical physical masks classes mapping)

end Shared.PNP.Record285.OwnershipCore
