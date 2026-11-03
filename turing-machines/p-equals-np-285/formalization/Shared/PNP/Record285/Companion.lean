import Shared.PNP.Record285.Machine
import Shared.PNP.Record285.Quotient

/-! The 286-state B-exit companion and its event-coloured quotient candidate.
The executable checker is a diagnostic until its result is proved in Lean. -/
namespace Shared.PNP.Record285.Companion
open Shared.Beeping.Machines
open Shared.PNP.Record285.Quotient

def literal : String := include_str "companion.tm"

def parseRow (line : List Char) : Option RawRow :=
  Record285.parseRow (line ++ [' ', '0'])

def parse : Option (List RawRow) := do
  let lines := splitChars '\n' literal.toList
  guard (lines.take 6 = ["#! format beeper-v1".toList, "#! states 286".toList,
    "#! start 0".toList, "#! beep 1".toList, "#! blank 0".toList, "#! head 0".toList])
  let rest := lines.drop 6
  guard (rest.getLast? = some [])
  rest.dropLast.mapM parseRow

def wellFormed (rows : List RawRow) : Bool :=
  rows.length == 572 && (rows.zipIdx.all fun (row,i) =>
    row.state == i/2 && row.read == i%2 && row.write < 2 && row.next < 286 && row.event == 0)

def rows : List RawRow := parse.getD []
def rowAt (i : Nat) : RawRow := rows[i]?.getD Record285.defaultRow

def physicalRow (r : RawRow) : Row 286 :=
  ⟨r.write == 1, r.move, ⟨r.next % 286, Nat.mod_lt _ (by decide)⟩, false⟩

def table : Table 286 := ⟨Vector.ofFn fun q =>
  (physicalRow (rowAt (2*q.val)), physicalRow (rowAt (2*q.val+1)))⟩

def machine : Machine 286 := ⟨table, ⟨0,by decide⟩, false, 0⟩

def beepState : Fin 286 := ⟨1,by decide⟩

/-- The frozen quotient merges exactly source states 1 and 117, with all
other states in numerical order. -/
def quotientMap (q : Fin 286) : Fin 285 :=
  ⟨if q.val = 117 then 1 else if q.val < 117 then q.val else q.val-1, by
    have hq := q.isLt
    split
    · omega
    · split <;> omega⟩

theorem quotientMap_one_preimages (q : Fin 286) :
    (quotientMap q).val = 1 ↔ q.val = 1 ∨ q.val = 117 := by
  unfold quotientMap
  dsimp only
  split
  · omega
  · split <;> omega


/-- The only distinct source states identified by this map are 1 and 117. -/
theorem quotientMap_eq_iff (a b : Fin 286) :
    quotientMap a = quotientMap b ↔
      a = b ∨ (a.val = 1 ∧ b.val = 117) ∨ (a.val = 117 ∧ b.val = 1) := by
  simp only [Fin.ext_iff, quotientMap]
  have ha := a.isLt
  have hb := b.isLt
  repeat' (first | split | omega)


/-- If the finite check is proved, every B-ingress step has exactly one marked
step with related full configurations and the same event. -/
def marked_refinement_of_check
    (h : check (machine.entering beepState) Record285.machine quotientMap = true) :
    Shared.Beeping.EventRefinement (machine.entering beepState).system Record285.machine.system :=
  refinement (check_sound _ _ _ h)


/-- Each marked event is exactly one transition before its B-exit event. -/
theorem marked_beep_shift_of_check
    (h : check (machine.entering beepState) Record285.machine quotientMap = true)
    (t : Nat) :
    Record285.machine.system.BeepAt t ↔ (machine.exiting beepState).system.BeepAt (t+1) :=
  (beep_iff (check_sound _ _ _ h) t).trans (entering_exiting_shift machine beepState t)

/-- This theorem exposes the unresolved finite-certificate premise explicitly. -/
theorem marked_silence_of_check
    (h : check (machine.entering beepState) Record285.machine quotientMap = true) :
    Record285.machine.system.EventuallySilent ↔ (machine.exiting beepState).system.EventuallySilent :=
  checked_ingress_exit_silence machine Record285.machine beepState quotientMap h

theorem marked_infinite_of_check
    (h : check (machine.entering beepState) Record285.machine quotientMap = true) :
    Record285.machine.system.InfinitelyManyBeeps ↔ (machine.exiting beepState).system.InfinitelyManyBeeps :=
  checked_ingress_exit_infinite machine Record285.machine beepState quotientMap h

end Shared.PNP.Record285.Companion
