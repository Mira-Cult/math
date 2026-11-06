import Shared.Beeping.NPcoNP.Grammar284Types

/-! Finite, fuel-bounded grammar unfolding and jump contraction. This follows
the path conventions of the producer's `grammar_rotations.py:graph` and
`weak_grammar.py:core_graph`; the identification of their host-language code
with this definition is a separate proof obligation. -/
namespace Shared.Beeping.NPcoNP.Grammar284

abbrev Path := List Bool

structure Expansion where
  starts : Array (Path × Nat) := #[]
  leaves : Array (Path × String) := #[]
  deriving Inhabited, Repr

/-- Record each path's first leaf, expanding the DAG as an ordered tree.
Fuel bounds depth; the ancestor list rejects recursive grammar cycles. -/
def expand (nodes : Array (Leaf × Leaf)) : Nat → Leaf → Path → List Nat → Expansion → Option Expansion
  | 0, _, _, _, _ => none
  | fuel+1, leaf, path, ancestors, acc => do
      let acc := { acc with starts := acc.starts.push (path, acc.leaves.size) }
      match leaf with
      | .op name => pure { acc with leaves := acc.leaves.push (path, name) }
      | .node i => do
          if ancestors.contains i then none else
            let (a, b) ← nodes[i]?
            let left ← expand nodes fuel a (path ++ [false]) (i :: ancestors) acc
            expand nodes fuel b (path ++ [true]) (i :: ancestors) left

def resolve (starts : Array (Path × Nat)) (p : Path) : Option Nat :=
  if p == [true,true] || p.take 3 == [true,true,true] then some 0
  else (starts.find? fun entry => entry.1 == p).map Prod.snd

/-- Select a false edge backwards, with root-crossing excluded. -/
def successor (starts : Array (Path × Nat)) (p : Path) (skip : Nat) : Option Nat := do
  let candidates := p.zipIdx.reverse.filter fun e => e.2 ≥ 2 && !e.1
  let (_, i) ← candidates[skip]?
  resolve starts (p.take i ++ [true])

/-- Select a true edge backwards for a structured loop restart. -/
def restart (starts : Array (Path × Nat)) (p : Path) (skip : Nat) : Option Nat := do
  let candidates := p.zipIdx.reverse.filter fun e => e.2 ≥ 1 && e.1
  let (_, i) ← candidates[skip]?
  resolve starts (p.take (i+1))

structure Row where
  op : String
  targets : List Nat
  deriving DecidableEq, Repr, Inhabited

/-- Decimal parser expressed on characters, with no opaque string primitives. -/
def parseDigits (cs : List Char) : Option Nat := do
  if cs.isEmpty then none else
    cs.foldlM (fun n c =>
      if '0' ≤ c && c ≤ '9' then some (10 * n + (c.toNat - '0'.toNat))
      else none) 0

/-- Producer operation tags, decoded without relying on runtime-only string search. -/
inductive OperationTag where
  | break (n : Nat)
  | continue (n : Nat)
  | branch
  | other
  deriving DecidableEq, Repr

def operationTag (op : String) : Option OperationTag :=
  let cs := op.toList
  match cs with
  | '_' :: 'b' :: 'r' :: 'e' :: 'a' :: 'k' :: '.' :: ds =>
      (parseDigits ds).map .break
  | '_' :: 'c' :: 'o' :: 'n' :: 't' :: 'i' :: 'n' :: 'u' :: 'e' :: '.' :: ds =>
      (parseDigits ds).map .continue
  | _ =>
      if cs.reverse.take 6 == ['z', 'n', 'c', 'e', 'd', '.'] then some .branch
      else some .other

def fullRow (starts : Array (Path × Nat)) (entry : Path × String) : Option Row := do
  let (p, op) := entry
  match ← operationTag op with
  | .break k =>
      let dst ← successor starts p k
      pure ⟨"jump", [dst]⟩
  | .continue k =>
      let dst ← restart starts p k
      pure ⟨"jump", [dst]⟩
  | .branch =>
      let first ← successor starts p 0
      let second ← successor starts p 1
      pure ⟨op, [first, second]⟩
  | .other =>
      let first ← successor starts p 0
      pure ⟨op, [first]⟩

structure Numbering where
  map : Array (Option Nat)
  kept : Array Nat
  deriving Inhabited

def number (rows : Array Row) : Numbering :=
  rows.toList.zipIdx.foldl (fun acc (row, i) =>
    if row.op == "jump" then
      ⟨acc.map.push none, acc.kept⟩
    else
      ⟨acc.map.push (some acc.kept.size), acc.kept.push i⟩) ⟨#[], #[]⟩

/-- Contract an administrative chain, rejecting cycles and malformed rows.
The finite fuel is the full row count, so a successful chain must reach a
retained row without revisiting a jump. -/
def target (rows : Array Row) (mapping : Array (Option Nat)) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel+1, i => do
      let row ← rows[i]?
      if row.op == "jump" then
        match row.targets with
        | [j] => target rows mapping fuel j
        | _ => none
      else
        (mapping[i]?).join

structure Graph where
  entry : Nat
  rows : Array Row
  deriving DecidableEq, Repr

def contract (rows : Array Row) : Option Graph := do
  let numbering := number rows
  if numbering.kept.isEmpty then none else do
    -- Force a check on every jump, even those absent from the entry run.
    let _ ← (List.range rows.size).mapM fun i => target rows numbering.map (rows.size+1) i
    let entry ← target rows numbering.map (rows.size+1) 0
    let out ← numbering.kept.toList.mapM fun i => do
      let row ← rows[i]?
      let dst ← row.targets.mapM (target rows numbering.map (rows.size+1))
      pure ⟨row.op, dst⟩
    pure ⟨entry, out.toArray⟩

def fullGraph (g : Grammar) (fuel : Nat) : Option (Array Row) := do
  let e ← expand g.nodes fuel (.node g.root) [true,true,false] [] {}
  (← e.leaves.toList.mapM (fullRow e.starts)).toArray

def coreGraph (g : Grammar) (fuel : Nat) : Option Graph := do
  let rows ← fullGraph g fuel
  contract rows

end Shared.Beeping.NPcoNP.Grammar284
