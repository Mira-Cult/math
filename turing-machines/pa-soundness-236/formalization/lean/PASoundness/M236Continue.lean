import PASoundness.M236BlankThird
/-! Literal finite scans for the continue control states. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Continue
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

private theorem replicate_shift (n : Nat) (tail : List Bool) :
    List.replicate n false ++ false :: tail = false :: (List.replicate n false ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

/-- Any literal zero-loop row silently scans a finite zero run. -/
theorem scan_zeros (q : Fin 237)
    (hrow : raw.table.row q false = ⟨false, .left, q, false⟩)
    (hevent : rawLabels.at q false = none)
    (count : Nat) (head : Int) (left right : List Bool) :
    rawSystem.Block ⟨q, head, ⟨List.replicate count false ++ left, false :: right⟩⟩ count
      ⟨q, head - (count : Int), ⟨left, false :: (List.replicate count false ++ right)⟩⟩ [] := by
  induction count generalizing head right with
  | zero => simpa using WordEventSystem.Block.refl rawSystem ⟨q, head, ⟨left, false :: right⟩⟩
  | succ count ih =>
    have hs : rawSystem.step
        ⟨q, head, ⟨List.replicate (count + 1) false ++ left, false :: right⟩⟩ =
        (⟨q, head - 1, ⟨List.replicate count false ++ left, false :: false :: right⟩⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, hrow, hevent,
        Move.apply, moveLeft, List.replicate_succ]
    have hb := (WordEventSystem.Block.single rawSystem hs).trans rawSystem
      (ih (head - 1) (false :: right))
    have hh : head - 1 - (count : Int) = head - ((count + 1 : Nat) : Int) := by omega
    simpa only [List.nil_append, hh, Nat.add_comm 1 count, List.replicate_succ,
      List.cons_append, replicate_shift] using hb

def state (level : Fin 3) : Fin 237 := #v[72, 73, 74][level]
def destination (level : Fin 3) : Fin 237 := #v[64, 72, 73][level]
def markerWrite (level : Fin 3) : Bool := level = 0

theorem rows (level : Fin 3) :
    raw.table.row (state level) false = ⟨false, .left, state level, false⟩ ∧
    rawLabels.at (state level) false = none ∧
    raw.table.row (state level) true = ⟨markerWrite level, .left, destination level, false⟩ ∧
    rawLabels.at (state level) true = none := by
  have h : ∀ (level : Fin 3),
      raw.table.row (state level) false = ⟨false, .left, state level, false⟩ ∧
      rawLabels.at (state level) false = none ∧
      raw.table.row (state level) true = ⟨markerWrite level, .left, destination level, false⟩ ∧
      rawLabels.at (state level) true = none := by decide
  exact h level

/-- Each continue state crosses arbitrarily many zeros and exactly one marker.
The level determines whether the marker is erased. -/
theorem scan_marker (level : Fin 3) (count : Nat) (head : Int) (left right : List Bool) :
    rawSystem.Block
      ⟨state level, head, ⟨List.replicate count false ++ true :: left, false :: right⟩⟩
      (count + 2)
      ⟨destination level, head - (count : Int) - 2,
        moveLeft ⟨left, true :: false :: (List.replicate count false ++ right)⟩ (markerWrite level)⟩ [] := by
  obtain ⟨r0,e0,r1,e1⟩ := rows level
  have hscan := scan_zeros (state level) r0 e0 count head (true :: left) right
  have hs0 : rawSystem.step
      ⟨state level, head - (count : Int), ⟨true :: left, false :: (List.replicate count false ++ right)⟩⟩ =
      (⟨state level, head - (count : Int) - 1, ⟨left, true :: false :: (List.replicate count false ++ right)⟩⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, r0, e0, Move.apply, moveLeft]
  have hs1 : rawSystem.step
      ⟨state level, head - (count : Int) - 1, ⟨left, true :: false :: (List.replicate count false ++ right)⟩⟩ =
      (⟨destination level, head - (count : Int) - 2,
        moveLeft ⟨left, true :: false :: (List.replicate count false ++ right)⟩ (markerWrite level)⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, r1, e1, Move.apply]
    omega
  simpa using (hscan.trans rawSystem (WordEventSystem.Block.single rawSystem hs0)).trans rawSystem
    (WordEventSystem.Block.single rawSystem hs1)
/-- A continue state handles a finite zero run even when it is empty. -/
theorem scan_marker_any (level : Fin 3) (count : Nat) (head : Int)
    (left right : List Bool) (old : Bool) :
    rawSystem.Block
      ⟨state level, head, moveLeft ⟨List.replicate count false ++ true :: left, old :: right⟩ old⟩
      (count + 1)
      ⟨destination level, head - (count : Int) - 1,
        moveLeft ⟨left, true :: (List.replicate count false ++ old :: right)⟩ (markerWrite level)⟩ [] := by
  cases count with
  | zero =>
    obtain ⟨_,_,r1,e1⟩ := rows level
    have hs : rawSystem.step
        ⟨state level, head, ⟨left, true :: old :: right⟩⟩ =
        (⟨destination level, head - 1,
          moveLeft ⟨left, true :: old :: right⟩ (markerWrite level)⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, r1, e1, Move.apply]
    simpa [moveLeft] using WordEventSystem.Block.single rawSystem hs
  | succ count =>
    have hb := scan_marker level count head left (old :: right)
    have hh : head - (count : Int) - 2 = head - ((count + 1 : Nat) : Int) - 1 := by omega
    have ht : count + 2 = (count + 1) + 1 := by omega
    simpa [moveLeft, List.replicate_succ, List.cons_append, hh, ht] using hb

/-- State 73 crosses two finite marker-separated runs and reaches state 64. -/
theorem scan_two_markers (first second : Nat) (head : Int)
    (left right : List Bool) (old : Bool) :
    rawSystem.Block
      ⟨73, head, moveLeft ⟨List.replicate first false ++ true ::
        (List.replicate second false ++ true :: left), old :: right⟩ old⟩
      ((first + 1) + (second + 1))
      ⟨64, head - (first : Int) - 1 - (second : Int) - 1,
        moveLeft ⟨left, true :: (List.replicate second false ++ false ::
          (List.replicate first false ++ old :: right))⟩ true⟩ [] := by
  have h1 := scan_marker_any 1 first head
    (List.replicate second false ++ true :: left) right old
  have h2 := scan_marker_any 0 second (head - (first : Int) - 1) left
    (List.replicate first false ++ old :: right) false
  have h1' : rawSystem.Block
      ⟨73, head, moveLeft ⟨List.replicate first false ++ true ::
        (List.replicate second false ++ true :: left), old :: right⟩ old⟩ (first + 1)
      ⟨72, head - (first : Int) - 1, moveLeft
        ⟨List.replicate second false ++ true :: left,
          false :: (List.replicate first false ++ old :: right)⟩ false⟩ [] := by
    simpa [state, destination, markerWrite, moveLeft] using h1
  have h2' : rawSystem.Block
      ⟨72, head - (first : Int) - 1, moveLeft
        ⟨List.replicate second false ++ true :: left,
          false :: (List.replicate first false ++ old :: right)⟩ false⟩ (second + 1)
      ⟨64, head - (first : Int) - 1 - (second : Int) - 1,
        moveLeft ⟨left, true :: (List.replicate second false ++ false ::
          (List.replicate first false ++ old :: right))⟩ true⟩ [] := by
    simpa [state, destination, markerWrite] using h2
  simpa using h1'.trans rawSystem h2'

/-- State 74 crosses three finite marker-separated runs and reaches state 64. -/
theorem scan_three_markers (first second third : Nat) (head : Int)
    (left right : List Bool) (old : Bool) :
    rawSystem.Block
      ⟨74, head, moveLeft ⟨List.replicate first false ++ true ::
        (List.replicate second false ++ true :: (List.replicate third false ++ true :: left)),
        old :: right⟩ old⟩
      ((first + 1) + ((second + 1) + (third + 1)))
      ⟨64, head - (first : Int) - 1 - (second : Int) - 1 - (third : Int) - 1,
        moveLeft ⟨left, true :: (List.replicate third false ++ false ::
          (List.replicate second false ++ false :: (List.replicate first false ++ old :: right)))⟩ true⟩ [] := by
  have h1 := scan_marker_any 2 first head
    (List.replicate second false ++ true :: (List.replicate third false ++ true :: left)) right old
  have h2 := scan_two_markers second third (head - (first : Int) - 1) left
    (List.replicate first false ++ old :: right) false
  have h1' : rawSystem.Block
      ⟨74, head, moveLeft ⟨List.replicate first false ++ true ::
        (List.replicate second false ++ true :: (List.replicate third false ++ true :: left)), old :: right⟩ old⟩
      (first + 1)
      ⟨73, head - (first : Int) - 1, moveLeft
        ⟨List.replicate second false ++ true :: (List.replicate third false ++ true :: left),
          false :: (List.replicate first false ++ old :: right)⟩ false⟩ [] := by
    simpa [state, destination, markerWrite, moveLeft] using h1
  simpa using h1'.trans rawSystem h2

/-- Lift any silent raw zipper block to the complete raw tape and exact quotient. -/
theorem physical_silent_block (start stop : Configuration 237) (steps : Nat)
    (hb : rawSystem.Block start steps stop []) (c : Config 237) (hrel : Related start c) :
    ∃ finish, (machineWordSystem raw rawLabels).Block c steps finish [] ∧
      Related stop finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) steps (mapConfig finish) [] := by
  have hs := advance_sound raw rawLabels hrel steps
  change Related (rawSystem.advance start steps) _ ∧ rawSystem.wordFrom start steps = _ at hs
  rw [hb.endpoint, hb.output] at hs
  let finish := (machineWordSystem raw rawLabels).advance c steps
  have hp : (machineWordSystem raw rawLabels).Block c steps finish [] := ⟨rfl, hs.2.symm⟩
  exact ⟨finish, hp, hs.1, BootstrapScan.mapped_block hp⟩

/-- Two continue markers are traversed on the complete tape in positive time. -/
theorem physical_two_markers (first second : Nat) (head : Int)
    (left right : List Bool) (old : Bool) (c : Config 237)
    (hrel : Related
      ⟨73, head, moveLeft ⟨List.replicate first false ++ true ::
        (List.replicate second false ++ true :: left), old :: right⟩ old⟩ c) :
    ∃ finish, (machineWordSystem raw rawLabels).Block c ((first + 1) + (second + 1)) finish [] ∧
      Related ⟨64, head - (first : Int) - 1 - (second : Int) - 1,
        moveLeft ⟨left, true :: (List.replicate second false ++ false ::
          (List.replicate first false ++ old :: right))⟩ true⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        ((first + 1) + (second + 1)) (mapConfig finish) [] ∧ 0 < (first + 1) + (second + 1) := by
  obtain ⟨finish, hp, hr, hq⟩ := physical_silent_block _ _ _
    (scan_two_markers first second head left right old) c hrel
  exact ⟨finish, hp, hr, hq, by omega⟩

/-- Three continue markers are traversed on the complete tape in positive time. -/
theorem physical_three_markers (first second third : Nat) (head : Int)
    (left right : List Bool) (old : Bool) (c : Config 237)
    (hrel : Related
      ⟨74, head, moveLeft ⟨List.replicate first false ++ true ::
        (List.replicate second false ++ true :: (List.replicate third false ++ true :: left)),
        old :: right⟩ old⟩ c) :
    ∃ finish, (machineWordSystem raw rawLabels).Block c
        ((first + 1) + ((second + 1) + (third + 1))) finish [] ∧
      Related ⟨64, head - (first : Int) - 1 - (second : Int) - 1 - (third : Int) - 1,
        moveLeft ⟨left, true :: (List.replicate third false ++ false ::
          (List.replicate second false ++ false :: (List.replicate first false ++ old :: right)))⟩ true⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        ((first + 1) + ((second + 1) + (third + 1))) (mapConfig finish) [] ∧
      0 < (first + 1) + ((second + 1) + (third + 1)) := by
  obtain ⟨finish, hp, hr, hq⟩ := physical_silent_block _ _ _
    (scan_three_markers first second third head left right old) c hrel
  exact ⟨finish, hp, hr, hq, by omega⟩

/-- Continue the literal return counter to the grammar root when its exact
root-prefix condition holds. The condition is exposed, not assumed globally. -/
theorem counter_to_root (runs : List (Fin 6)) (bit : Bool) (rootTail : List Bool)
    (head : Int) (left right : List Bool) (c : Config 237)
    (hroot : counterPush runs right = true :: bit :: rootTail)
    (hrel : Related
      ⟨64, head, moveLeft ⟨counterWord runs ++ List.replicate 6 false ++ false :: left,
        true :: right⟩ true⟩ c) :
    ∃ finish, (machineWordSystem raw rawLabels).Block c (counterTime runs + 6 + 10) finish [] ∧
      Related ⟨79, head - (counterTime runs : Int) - 6 + 10,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left), rootTail⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) (counterTime runs + 6 + 10)
        (mapConfig finish) [] ∧ 0 < counterTime runs + 6 + 10 := by
  obtain ⟨mid, hp, hr, hq, _⟩ := physical_counter runs head (false :: left) right c hrel
  rw [hroot] at hr
  have hr0 : Related ⟨65, head - (counterTime runs : Int) - 6,
      ⟨left, List.replicate 7 false ++ true :: true :: bit :: rootTail⟩⟩ mid := by
    simpa [moveLeft, List.replicate_succ] using hr
  have hb := root_reentry 7 bit (head - (counterTime runs : Int) - 6) left rootTail
  obtain ⟨finish, hp', hr'⟩ := BulkSweep.physical_block raw rawLabels _ _ mid 10 hr0 hb
  refine ⟨finish, ?_, ?_, ?_, by omega⟩
  · simpa using hp.trans (machineWordSystem raw rawLabels) hp'
  · change Related ⟨79, head - (counterTime runs : Int) - 6 + 7 + 3,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left), rootTail⟩⟩ finish at hr'
    have hh : head - (counterTime runs : Int) - 6 + 7 + 3 =
        head - (counterTime runs : Int) - 6 + 10 := by omega
    rw [hh] at hr'
    exact hr'
  · simpa using hq.trans (machineWordSystem machine machineLabels) (BootstrapScan.mapped_block hp')

/-- A one-marker continue and the return counter compose to the grammar root. -/
theorem physical_one_to_root (first : Nat) (runs : List (Fin 6))
    (bit : Bool) (rootTail : List Bool) (head : Int) (left right : List Bool)
    (old : Bool) (c : Config 237)
    (hroot : counterPush runs (List.replicate first false ++ old :: right) = true :: bit :: rootTail)
    (hrel : Related
      ⟨72, head, moveLeft ⟨List.replicate first false ++ true ::
        (counterWord runs ++ List.replicate 6 false ++ false :: left), old :: right⟩ old⟩ c) :
    ∃ finish, (machineWordSystem raw rawLabels).Block c
        (first + 1 + (counterTime runs + 6 + 10)) finish [] ∧
      Related ⟨79, head - (first : Int) - 1 - (counterTime runs : Int) - 6 + 10,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left), rootTail⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (first + 1 + (counterTime runs + 6 + 10)) (mapConfig finish) [] ∧
      0 < first + 1 + (counterTime runs + 6 + 10) := by
  have hb := scan_marker_any 0 first head
    (counterWord runs ++ List.replicate 6 false ++ false :: left) right old
  have hb' : rawSystem.Block
      ⟨72, head, moveLeft ⟨List.replicate first false ++ true ::
        (counterWord runs ++ List.replicate 6 false ++ false :: left), old :: right⟩ old⟩
      (first + 1)
      ⟨64, head - (first : Int) - 1, moveLeft
        ⟨counterWord runs ++ List.replicate 6 false ++ false :: left,
          true :: (List.replicate first false ++ old :: right)⟩ true⟩ [] := by
    simpa [state, destination, markerWrite] using hb
  obtain ⟨mid, hp, hr, hq⟩ := physical_silent_block _ _ _ hb' c hrel
  obtain ⟨finish, hp', hr', hq', _⟩ := counter_to_root runs bit rootTail
    (head - (first : Int) - 1) left (List.replicate first false ++ old :: right) mid hroot hr
  exact ⟨finish, by simpa using hp.trans (machineWordSystem raw rawLabels) hp', hr',
    by simpa using hq.trans (machineWordSystem machine machineLabels) hq', by omega⟩

/-- A two-marker continue and the return counter compose to the grammar root
under the displayed complete-tape and root-prefix conditions. -/
theorem physical_two_to_root (first second : Nat) (runs : List (Fin 6))
    (bit : Bool) (rootTail : List Bool) (head : Int) (left right : List Bool)
    (old : Bool) (c : Config 237)
    (hroot : counterPush runs (List.replicate second false ++ false ::
      (List.replicate first false ++ old :: right)) = true :: bit :: rootTail)
    (hrel : Related
      ⟨73, head, moveLeft ⟨List.replicate first false ++ true ::
        (List.replicate second false ++ true ::
          (counterWord runs ++ List.replicate 6 false ++ false :: left)), old :: right⟩ old⟩ c) :
    ∃ finish, (machineWordSystem raw rawLabels).Block c
        ((first + 1) + (second + 1) + (counterTime runs + 6 + 10)) finish [] ∧
      Related ⟨79, head - (first : Int) - 1 - (second : Int) - 1 -
        (counterTime runs : Int) - 6 + 10,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left), rootTail⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        ((first + 1) + (second + 1) + (counterTime runs + 6 + 10)) (mapConfig finish) [] ∧
      0 < (first + 1) + (second + 1) + (counterTime runs + 6 + 10) := by
  obtain ⟨mid, hp, hr, hq, _⟩ := physical_two_markers first second head
    (counterWord runs ++ List.replicate 6 false ++ false :: left) right old c hrel
  obtain ⟨finish, hp', hr', hq', _⟩ := counter_to_root runs bit rootTail
    (head - (first : Int) - 1 - (second : Int) - 1) left
    (List.replicate second false ++ false :: (List.replicate first false ++ old :: right)) mid hroot hr
  exact ⟨finish, by simpa using hp.trans (machineWordSystem raw rawLabels) hp', hr',
    by simpa using hq.trans (machineWordSystem machine machineLabels) hq', by omega⟩

/-- A three-marker continue and the return counter compose to the grammar root
under the displayed complete-tape and root-prefix conditions. -/
theorem physical_three_to_root (first second third : Nat) (runs : List (Fin 6))
    (bit : Bool) (rootTail : List Bool) (head : Int) (left right : List Bool)
    (old : Bool) (c : Config 237)
    (hroot : counterPush runs (List.replicate third false ++ false ::
      (List.replicate second false ++ false :: (List.replicate first false ++ old :: right))) =
      true :: bit :: rootTail)
    (hrel : Related
      ⟨74, head, moveLeft ⟨List.replicate first false ++ true ::
        (List.replicate second false ++ true :: (List.replicate third false ++ true ::
          (counterWord runs ++ List.replicate 6 false ++ false :: left))), old :: right⟩ old⟩ c) :
    ∃ finish, (machineWordSystem raw rawLabels).Block c
        ((first + 1) + ((second + 1) + (third + 1)) + (counterTime runs + 6 + 10)) finish [] ∧
      Related ⟨79, head - (first : Int) - 1 - (second : Int) - 1 - (third : Int) - 1 -
        (counterTime runs : Int) - 6 + 10,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left), rootTail⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        ((first + 1) + ((second + 1) + (third + 1)) + (counterTime runs + 6 + 10)) (mapConfig finish) [] ∧
      0 < (first + 1) + ((second + 1) + (third + 1)) + (counterTime runs + 6 + 10) := by
  obtain ⟨mid, hp, hr, hq, _⟩ := physical_three_markers first second third head
    (counterWord runs ++ List.replicate 6 false ++ false :: left) right old c hrel
  obtain ⟨finish, hp', hr', hq', _⟩ := counter_to_root runs bit rootTail
    (head - (first : Int) - 1 - (second : Int) - 1 - (third : Int) - 1) left
    (List.replicate third false ++ false :: (List.replicate second false ++ false ::
      (List.replicate first false ++ old :: right))) mid hroot hr
  exact ⟨finish, by simpa using hp.trans (machineWordSystem raw rawLabels) hp', hr',
    by simpa using hq.trans (machineWordSystem machine machineLabels) hq', by omega⟩

/-- The complete unbounded two-way tape follows the same silent marker scan
in the raw table and in the exact quotient, with positive duration. -/
theorem physical_scan_marker (level : Fin 3) (count : Nat) (head : Int)
    (left right : List Bool) (c : Config 237)
    (hrel : Related
      ⟨state level, head, ⟨List.replicate count false ++ true :: left, false :: right⟩⟩ c) :
    ∃ finish,
      (machineWordSystem raw rawLabels).Block c (count + 2) finish [] ∧
      Related ⟨destination level, head - (count : Int) - 2,
        moveLeft ⟨left, true :: false :: (List.replicate count false ++ right)⟩ (markerWrite level)⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) (count + 2) (mapConfig finish) [] ∧
      0 < count + 2 := by
  have hb := scan_marker level count head left right
  have hs := advance_sound raw rawLabels hrel (count + 2)
  change Related (rawSystem.advance
      ⟨state level, head, ⟨List.replicate count false ++ true :: left, false :: right⟩⟩ (count + 2)) _ ∧
    rawSystem.wordFrom
      ⟨state level, head, ⟨List.replicate count false ++ true :: left, false :: right⟩⟩ (count + 2) = _ at hs
  rw [hb.endpoint, hb.output] at hs
  let finish := (machineWordSystem raw rawLabels).advance c (count + 2)
  have hp : (machineWordSystem raw rawLabels).Block c (count + 2) finish [] := ⟨rfl, hs.2.symm⟩
  exact ⟨finish, hp, hs.1, BootstrapScan.mapped_block hp, by omega⟩
/-- A finite polarity and duration control for the two-marker scan. -/
example : rawSystem.Block
    ⟨73, 0, ⟨[true, false], [true, false]⟩⟩ 2
    ⟨64, -2, ⟨[], [false, true, false, false]⟩⟩ [] := by
  constructor <;> decide

example : ¬ rawSystem.Block
    ⟨73, 0, ⟨[true, false], [true, false]⟩⟩ 1
    ⟨64, -2, ⟨[], [false, true, false, false]⟩⟩ [] := by
  intro h
  have bad : rawSystem.advance ⟨73, 0, ⟨[true, false], [true, false]⟩⟩ 1 ≠
      ⟨64, -2, ⟨[], [false, true, false, false]⟩⟩ := by decide
  exact bad h.endpoint
end PASoundness.M236.Continue
