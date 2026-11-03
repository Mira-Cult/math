import Shared.PNP.Record285.GrammarCoreSemantics
import Shared.PNP.Record285.ProjectionData

/-! Executable leaf semantics and finite graph checker for a producer grammar.
The checker rejects missing continuations and exhausted administrative runs. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.ProducerGrammar
open Shared.Beeping
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarPure
open Shared.PNP.Record285.GrammarControlGraph
open Shared.PNP.Record285.OwnershipCore

structure Data where
  nodes : Array Node
  names : Array String
  root : Nat

def edgeAt (g : Data) (n : Nat) (b : Bool) : Option Edge :=
  (g.nodes[n]?).map (fun p => if b then p.2 else p.1)

def walk (g : Data) (n : Nat) : List Bool → Option Edge
  | [] => none
  | b::bs =>
    match edgeAt g n b with
    | none => none
    | some (.node j) => walk g j bs
    | some e => if bs.isEmpty then some e else none

def descend (g : Data) : Nat → Nat → (Nat → Bool) → Nat → Option (Edge × Nat)
  | 0,_,_,_ => none
  | fuel+1,n,input,pos =>
    match edgeAt g n (input pos) with
    | none => none
    | some (.node j) => descend g fuel j input (pos+1)
    | some e => some (e,pos+1)

def successor (g : Data) (e : Edge) (code : List Bool) (branch : Bool) : Option (List Bool) := do
  let control ← transfer e code branch
  let (_,len) ← descend g (g.nodes.size+1) g.root (pureBits control) 0
  pure (window (pureBits control) 0 len)

def administrative : Edge → Bool
  | .brk _ | .cont _ => true
  | _ => false

def action : Edge → Option Action
  | .inc n => some (.inc n)
  | .dec n => some (.dec n)
  | .half n => some (.half n)
  | .beep => some .beep
  | _ => none

def settle (g : Data) : Nat → List Bool → Option (List Bool)
  | 0,_ => none
  | fuel+1,pc => do
    let e ← walk g g.root pc
    if administrative e then
      let next ← successor g e pc false
      settle g fuel next
    else pure pc

def checkRow (g : Data) (rows : Array OwnershipCore.Row) (positions : Array (List Bool)) (i : Nat) : Bool :=
  match rows[i]?, positions[i]? with
  | some row, some pc =>
    match walk g g.root pc, positions[row.no]?, positions[row.yes]? with
    | some e, some no, some yes =>
      decide (action e = some row.action) &&
      decide ((successor g e pc false).bind (settle g 32) = some no) &&
      decide ((successor g e pc true).bind (settle g 32) = some yes)
    | _,_,_ => false
  | _,_ => false

def check (g : Data) (rows : Array OwnershipCore.Row) (positions : Array (List Bool)) : Bool :=
  decide (rows.size = positions.size) && decide (positions[0]? = some [false]) &&
  (List.range rows.size).all (checkRow g rows positions)

/-- Each accepted row identifies the literal grammar operation and both
successors, after a bounded number of silent administrative actions. -/
theorem check_at (g : Data) (rows : Array OwnershipCore.Row) (positions : Array (List Bool))
    (h : check g rows positions = true) (i : Nat) (hi : i < rows.size) :
    checkRow g rows positions i = true := by
  have ha : (List.range rows.size).all (checkRow g rows positions) = true := by
    simp only [check,Bool.and_eq_true_iff] at h
    exact h.2
  exact List.all_eq_true.mp ha i (List.mem_range.mpr hi)

end Shared.PNP.Record285.ProducerGrammar
