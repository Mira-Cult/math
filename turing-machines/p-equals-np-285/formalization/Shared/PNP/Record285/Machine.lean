import Shared.PNP.Record285.Table

/-! The actual 285-state table in the shared integer-tape semantics. Each row
is decoded from the embedded literal text. -/
namespace Shared.PNP.Record285

open Shared.Beeping.Machines

def rows : List RawRow := parse.getD []

def defaultRow : RawRow := ⟨0,0,0,.left,0,0⟩

def rowAt (i : Nat) : RawRow := rows[i]?.getD defaultRow

def physicalRow (r : RawRow) : Row 285 :=
  ⟨r.write == 1, r.move, ⟨r.next % 285, Nat.mod_lt _ (by decide)⟩, r.event == 1⟩

def table : Table 285 := ⟨Vector.ofFn fun q =>
  (physicalRow (rowAt (2*q.val)), physicalRow (rowAt (2*q.val+1)))⟩

def machine : Machine 285 := ⟨table, ⟨0, by decide⟩, false, 0⟩

/-- An indexed parse result determines the corresponding physical row. This
exposes the parsing premise until a kernel-checked finite certificate proves it. -/
theorem row_from_parse (parsed : List RawRow) (hparse : parse = some parsed)
    (q : Fin 285) (r : RawRow) (read : Bool)
    (hrow : parsed[2*q.val + (if read then 1 else 0)]? = some r) :
    table.row q read = physicalRow r := by
  cases read <;> simp only [Bool.false_eq_true, if_false, Nat.add_zero, if_true] at hrow <;>
    simp [Table.row, table, rowAt, rows, hparse, hrow]

/-- Every finite prefix from the blank initial configuration has a next
configuration. Total physical execution alone does not prove source progress. -/
theorem perpetual (t : Nat) : ∃ c, machine.system.run (t+1) = c := ⟨_, rfl⟩

/-- Every physical step moves one tape cell; this still permits unbounded
administrative loops and therefore is not a source-progress theorem. -/
theorem head_moves (t : Nat) :
    (machine.system.run (t+1)).head = (machine.system.run t).head - 1 ∨
    (machine.system.run (t+1)).head = (machine.system.run t).head + 1 := by
  change (Machine.step machine (machine.system.run t)).1.head = _ ∨
    (Machine.step machine (machine.system.run t)).1.head = _
  simp only [Machine.step]
  cases (machine.table.row (machine.system.run t).state
    ((machine.system.run t).tape (machine.system.run t).head)).move <;>
      simp [Move.apply]

@[simp] theorem blank_start (x : Int) : machine.initial.tape x = false := rfl
@[simp] theorem start_state : machine.initial.state.val = 0 := rfl
@[simp] theorem start_head : machine.initial.head = 0 := rfl

end Shared.PNP.Record285
