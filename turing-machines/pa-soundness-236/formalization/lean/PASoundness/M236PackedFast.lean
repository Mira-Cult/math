import PASoundness.M236PackedTape

/-!
Executable row access separated from the packed checker. A concrete fast
lookup must be proved extensionally equal to the literal table before its
results can be used by `PackedTape.run_sound`.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.PackedFast

open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.PackedTape

structure Lookup (n : Nat) where
  row : Fin n → Bool → Row n
  event : Fin n → Bool → Option Bool

def ordinary {n : Nat} (m : Machine n) (labels : BitLabels n) : Lookup n :=
  ⟨m.table.row, labels.at⟩

def valid {n : Nat} (table : Lookup n) (q : Fin n) (first second : Bool)
    (direction : Move) : Prop :=
  let a := table.row q first
  let b := table.row a.next second
  a.move = direction ∧ b.move = direction ∧ b.next = q ∧
    table.event q first = none ∧ table.event a.next second = none

instance {n : Nat} (table : Lookup n) (q : Fin n) (a b : Bool) (d : Move) :
    Decidable (valid table q a b d) := by unfold valid; infer_instance

def step {n : Nat} (table : Lookup n) (c : Configuration n) : Configuration n × List Bool :=
  let (symbol, right) := pop c.tape.right
  let row := table.row c.state symbol
  let nextTape := match row.move with
    | .right => ⟨prependBit row.write c.tape.left, right⟩
    | .left =>
      let (newHead, left) := pop c.tape.left
      ⟨left, prependBit newHead (prependBit row.write right)⟩
  (⟨row.next, row.move.apply c.head, nextTape⟩, (table.event c.state symbol).toList)

def sweepRight {n : Nat} (table : Lookup n) (count : Nat)
    (c : Configuration n) : Option (Configuration n) :=
  match c.tape.right with
  | .pair first second k :: rest =>
    if 0 < count ∧ count ≤ k ∧ valid table c.state first second .right then
      let a := table.row c.state first
      let b := table.row a.next second
      some ⟨c.state, c.head + 2 * (count : Int),
        ⟨prependPairs b.write a.write count c.tape.left,
          .pair first second (k - count) :: rest⟩⟩
    else none
  | _ => none

def sweepLeft {n : Nat} (table : Lookup n) (count : Nat)
    (c : Configuration n) : Option (Configuration n) :=
  match c.tape.left with
  | .pair second first k :: rest =>
    let (symbol, right) := pop c.tape.right
    if hasHead c.tape.right = true ∧ symbol = first ∧ 0 < count ∧ count ≤ k ∧
        valid table c.state first second .left then
      let a := table.row c.state first
      let b := table.row a.next second
      some ⟨c.state, c.head - 2 * (count : Int),
        ⟨.pair second first (k - count) :: rest,
          prependBit first (prependPairs b.write a.write count right)⟩⟩
    else none
  | _ => none

def perform {n : Nat} (table : Lookup n) (c : Configuration n) :
    Op → Option (Configuration n × Nat × List Bool)
  | .one => some ((step table c).1, 1, (step table c).2)
  | .right count => (sweepRight table count c).map fun out => (out, 2 * count, [])
  | .left count => (sweepLeft table count c).map fun out => (out, 2 * count, [])

def run {n : Nat} (table : Lookup n) :
    Configuration n → List Op → Option (Configuration n × Nat × List Bool)
  | c, [] => some (c, 0, [])
  | c, op :: ops => do
      let (middle, t, w) ← perform table c op
      let (finish, u, v) ← run table middle ops
      some (finish, t + u, w ++ v)

theorem perform_ordinary {n : Nat} (m : Machine n) (labels : BitLabels n)
    (c : Configuration n) (op : Op) :
    perform (ordinary m labels) c op = PackedTape.perform m labels c op := by
  cases op <;> rfl

theorem run_ordinary {n : Nat} (m : Machine n) (labels : BitLabels n)
    (c : Configuration n) (ops : List Op) :
    run (ordinary m labels) c ops = PackedTape.run m labels c ops := by
  induction ops generalizing c with
  | nil => rfl
  | cons op ops ih =>
    simp only [run, PackedTape.run, perform_ordinary, ih]

end PASoundness.M236.PackedFast
