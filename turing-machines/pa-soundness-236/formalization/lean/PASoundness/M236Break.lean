import PASoundness.M236ContinueNext
/-! Literal finite scans for the break control states. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Break
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

private theorem replicate_shift (n : Nat) (tail : List Bool) :
    List.replicate n false ++ false :: tail = false :: (List.replicate n false ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

/-- A literal one-loop erases an arbitrary finite run while moving left. -/
theorem erase_ones (q : Fin 237)
    (hrow : raw.table.row q true = ⟨false, .left, q, false⟩)
    (hevent : rawLabels.at q true = none)
    (count : Nat) (head : Int) (left right : List Bool) :
    rawSystem.Block ⟨q, head, ⟨List.replicate count true ++ left, true :: right⟩⟩ count
      ⟨q, head - (count : Int), ⟨left, true :: (List.replicate count false ++ right)⟩⟩ [] := by
  induction count generalizing head right with
  | zero => simpa using WordEventSystem.Block.refl rawSystem ⟨q, head, ⟨left, true :: right⟩⟩
  | succ count ih =>
    have hs : rawSystem.step
        ⟨q, head, ⟨List.replicate (count + 1) true ++ left, true :: right⟩⟩ =
        (⟨q, head - 1, ⟨List.replicate count true ++ left, true :: false :: right⟩⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, hrow, hevent,
        Move.apply, moveLeft, List.replicate_succ]
    have hb := (WordEventSystem.Block.single rawSystem hs).trans rawSystem
      (ih (head - 1) (false :: right))
    have hh : head - 1 - (count : Int) = head - ((count + 1 : Nat) : Int) := by omega
    simpa only [List.nil_append, hh, Nat.add_comm 1 count, List.replicate_succ,
      List.cons_append, replicate_shift] using hb

def state (level : Fin 3) : Fin 237 := #v[69, 70, 71][level]
def destination (level : Fin 3) : Fin 237 := #v[68, 69, 70][level]

theorem rows (level : Fin 3) :
    raw.table.row (state level) true = ⟨false, .left, state level, false⟩ ∧
    rawLabels.at (state level) true = none ∧
    raw.table.row (state level) false = ⟨false, .left, destination level, false⟩ ∧
    rawLabels.at (state level) false = none := by
  have h : ∀ (level : Fin 3),
      raw.table.row (state level) true = ⟨false, .left, state level, false⟩ ∧
      rawLabels.at (state level) true = none ∧
      raw.table.row (state level) false = ⟨false, .left, destination level, false⟩ ∧
      rawLabels.at (state level) false = none := by decide
  exact h level

/-- Each break state erases a finite one-run and crosses one zero. -/
theorem cross_zero (level : Fin 3) (count : Nat) (head : Int)
    (left right : List Bool) (old : Bool) :
    rawSystem.Block
      ⟨state level, head, moveLeft ⟨List.replicate count true ++ false :: left, old :: right⟩ old⟩
      (count + 1)
      ⟨destination level, head - (count : Int) - 1,
        moveLeft ⟨left, false :: (List.replicate count false ++ old :: right)⟩ false⟩ [] := by
  obtain ⟨r1,e1,r0,e0⟩ := rows level
  cases count with
  | zero =>
    have hs : rawSystem.step
        ⟨state level, head, ⟨left, false :: old :: right⟩⟩ =
        (⟨destination level, head - 1,
          moveLeft ⟨left, false :: old :: right⟩ false⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, r0, e0, Move.apply]
    simpa [moveLeft] using WordEventSystem.Block.single rawSystem hs
  | succ count =>
    have hscan := erase_ones (state level) r1 e1 count head (false :: left) (old :: right)
    have hs1 : rawSystem.step
        ⟨state level, head - (count : Int), ⟨false :: left, true :: (List.replicate count false ++ old :: right)⟩⟩ =
        (⟨state level, head - (count : Int) - 1, ⟨left, false :: false :: (List.replicate count false ++ old :: right)⟩⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, r1, e1, Move.apply, moveLeft]
    have hs0 : rawSystem.step
        ⟨state level, head - (count : Int) - 1, ⟨left, false :: false :: (List.replicate count false ++ old :: right)⟩⟩ =
        (⟨destination level, head - (count : Int) - 2,
          moveLeft ⟨left, false :: false :: (List.replicate count false ++ old :: right)⟩ false⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, r0, e0, Move.apply]
      omega
    have hb := (hscan.trans rawSystem (WordEventSystem.Block.single rawSystem hs1)).trans rawSystem
      (WordEventSystem.Block.single rawSystem hs0)
    have hh : head - (count : Int) - 2 = head - ((count + 1 : Nat) : Int) - 1 := by omega
    have ht : count + 2 = (count + 1) + 1 := by omega
    simpa [moveLeft, List.replicate_succ, List.cons_append, hh, ht] using hb
/-- Raw state 70 crosses two zero markers, erasing both intervening one-runs. -/
theorem cross_two (first second : Nat) (head : Int) (left right : List Bool) (old : Bool) :
    rawSystem.Block
      ⟨70, head, moveLeft ⟨List.replicate first true ++ false ::
        (List.replicate second true ++ false :: left), old :: right⟩ old⟩
      ((first + 1) + (second + 1))
      ⟨68, head - (first : Int) - 1 - (second : Int) - 1,
        moveLeft ⟨left, false :: (List.replicate second false ++ false ::
          (List.replicate first false ++ old :: right))⟩ false⟩ [] := by
  have h1 := cross_zero 1 first head (List.replicate second true ++ false :: left) right old
  have h2 := cross_zero 0 second (head - (first : Int) - 1) left
    (List.replicate first false ++ old :: right) false
  have h1' : rawSystem.Block
      ⟨70, head, moveLeft ⟨List.replicate first true ++ false ::
        (List.replicate second true ++ false :: left), old :: right⟩ old⟩ (first + 1)
      ⟨69, head - (first : Int) - 1, moveLeft
        ⟨List.replicate second true ++ false :: left,
          false :: (List.replicate first false ++ old :: right)⟩ false⟩ [] := by
    simpa [state, destination, moveLeft] using h1
  have h2' : rawSystem.Block
      ⟨69, head - (first : Int) - 1, moveLeft
        ⟨List.replicate second true ++ false :: left,
          false :: (List.replicate first false ++ old :: right)⟩ false⟩ (second + 1)
      ⟨68, head - (first : Int) - 1 - (second : Int) - 1,
        moveLeft ⟨left, false :: (List.replicate second false ++ false ::
          (List.replicate first false ++ old :: right))⟩ false⟩ [] := by
    simpa [state, destination] using h2
  simpa using h1'.trans rawSystem h2'

/-- Raw state 71 crosses three zero markers and reaches cleanup state 68. -/
theorem cross_three (first second third : Nat) (head : Int) (left right : List Bool) (old : Bool) :
    rawSystem.Block
      ⟨71, head, moveLeft ⟨List.replicate first true ++ false ::
        (List.replicate second true ++ false :: (List.replicate third true ++ false :: left)), old :: right⟩ old⟩
      ((first + 1) + ((second + 1) + (third + 1)))
      ⟨68, head - (first : Int) - 1 - (second : Int) - 1 - (third : Int) - 1,
        moveLeft ⟨left, false :: (List.replicate third false ++ false ::
          (List.replicate second false ++ false :: (List.replicate first false ++ old :: right)))⟩ false⟩ [] := by
  have h1 := cross_zero 2 first head
    (List.replicate second true ++ false :: (List.replicate third true ++ false :: left)) right old
  have h2 := cross_two second third (head - (first : Int) - 1) left
    (List.replicate first false ++ old :: right) false
  have h1' : rawSystem.Block
      ⟨71, head, moveLeft ⟨List.replicate first true ++ false ::
        (List.replicate second true ++ false :: (List.replicate third true ++ false :: left)), old :: right⟩ old⟩
      (first + 1)
      ⟨70, head - (first : Int) - 1, moveLeft
        ⟨List.replicate second true ++ false :: (List.replicate third true ++ false :: left),
          false :: (List.replicate first false ++ old :: right)⟩ false⟩ [] := by
    simpa [state, destination, moveLeft] using h1
  simpa using h1'.trans rawSystem h2

/-- A break marker scan refines the exact raw and quotient full-tape machines. -/
theorem physical_cross_zero (level : Fin 3) (count : Nat) (head : Int)
    (left right : List Bool) (old : Bool) (c : Config 237)
    (hrel : Related
      ⟨state level, head, moveLeft ⟨List.replicate count true ++ false :: left, old :: right⟩ old⟩ c) :
    ∃ finish, (machineWordSystem raw rawLabels).Block c (count + 1) finish [] ∧
      Related ⟨destination level, head - (count : Int) - 1,
        moveLeft ⟨left, false :: (List.replicate count false ++ old :: right)⟩ false⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) (count + 1) (mapConfig finish) [] ∧
      0 < count + 1 := by
  obtain ⟨finish, hp, hr, hq⟩ := Continue.physical_silent_block _ _ _
    (cross_zero level count head left right old) c hrel
  exact ⟨finish, hp, hr, hq, by omega⟩
/-- From cleanup state 68, erase the finite left run and scan across an
arbitrary zero gap to restore the zero-valued unary anchor. -/
theorem cleanup_zero_anchor (scratch gap : Nat) (head : Int) (left tail : List Bool) :
    rawSystem.Block
      ⟨68, head, moveLeft ⟨List.replicate scratch true ++ false :: left,
        false :: (List.replicate gap false ++ true :: false :: tail)⟩ false⟩
      (3 * scratch + 2 * gap + 7)
      ⟨64, head - (scratch : Int) - 1,
        moveLeft ⟨left, true :: (List.replicate (scratch + 1 + gap) false ++ true :: false :: tail)⟩ true⟩ [] := by
  have hfirst := UnaryCleanup.erase_left_stop scratch head left
    (List.replicate gap false ++ true :: false :: tail)
  let count := scratch + 1 + gap
  have hfirst' : rawSystem.Block
      ⟨68, head, moveLeft ⟨List.replicate scratch true ++ false :: left,
        false :: (List.replicate gap false ++ true :: false :: tail)⟩ false⟩ (scratch + 1)
      ⟨39, head - (scratch : Int) + 1,
        ⟨true :: left, List.replicate count false ++ true :: false :: tail⟩⟩ [] := by
    have hz : List.replicate scratch false ++ false :: (List.replicate gap false ++ true :: false :: tail) =
        List.replicate count false ++ true :: false :: tail := by
      dsimp [count]
      calc
        _ = (List.replicate scratch false ++ List.replicate 1 false ++ List.replicate gap false) ++
            true :: false :: tail := by simp [List.append_assoc]
        _ = _ := by rw [List.replicate_append_replicate, List.replicate_append_replicate]
    simpa only [hz] using hfirst
  have hseek := UnaryCleanup.seek_and_erase count 0 (head - (scratch : Int) + 1) (true :: left) tail
  have hseek' : rawSystem.Block
      ⟨39, head - (scratch : Int) + 1,
        ⟨true :: left, List.replicate count false ++ true :: false :: tail⟩⟩ (count + 0 + 2)
      ⟨1, head - (scratch : Int) + 1 + (count : Int),
        ⟨List.replicate count false ++ true :: left, false :: false :: tail⟩⟩ [] := by
    simpa [moveLeft] using hseek
  have hrestore := restore_and_scan count (head - (scratch : Int) + 1 + (count : Int)) left (false :: tail)
  have hb := (hfirst'.trans rawSystem hseek').trans rawSystem hrestore
  have ht : scratch + 1 + (count + 0 + 2) + (count + 2) = 3 * scratch + 2 * gap + 7 := by
    dsimp [count]; omega
  have hh : head - (scratch : Int) + 1 + (count : Int) - (count : Int) - 2 =
      head - (scratch : Int) - 1 := by omega
  simpa only [List.nil_append, ht, hh] using hb
/-- The generalized cleanup block refines the raw and exact quotient tapes. -/
theorem physical_cleanup_zero_anchor (scratch gap : Nat) (head : Int)
    (left tail : List Bool) (c : Config 237)
    (hrel : Related
      ⟨68, head, moveLeft ⟨List.replicate scratch true ++ false :: left,
        false :: (List.replicate gap false ++ true :: false :: tail)⟩ false⟩ c) :
    ∃ finish, (machineWordSystem raw rawLabels).Block c (3 * scratch + 2 * gap + 7) finish [] ∧
      Related ⟨64, head - (scratch : Int) - 1,
        moveLeft ⟨left, true :: (List.replicate (scratch + 1 + gap) false ++ true :: false :: tail)⟩ true⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (3 * scratch + 2 * gap + 7) (mapConfig finish) [] ∧ 0 < 3 * scratch + 2 * gap + 7 := by
  obtain ⟨finish, hp, hr, hq⟩ := Continue.physical_silent_block _ _ _
    (cleanup_zero_anchor scratch gap head left tail) c hrel
  exact ⟨finish, hp, hr, hq, by omega⟩

/-- A prepared one-marker break, cleanup and counter return reach the root
silently under the explicit finite control-prefix condition. -/
theorem physical_one_to_root (first scratch gap : Nat) (runs : List (Fin 6))
    (bit : Bool) (rootTail : List Bool) (head : Int) (left tail : List Bool) (c : Config 237)
    (hroot : counterPush runs
      (List.replicate (scratch + 1 + (first + 1 + gap)) false ++ true :: false :: tail) =
      true :: bit :: rootTail)
    (hrel : Related
      ⟨69, head, moveLeft ⟨List.replicate first true ++ false ::
        (List.replicate scratch true ++ false ::
          (counterWord runs ++ List.replicate 6 false ++ false :: left)),
        false :: (List.replicate gap false ++ true :: false :: tail)⟩ false⟩ c) :
    ∃ finish, (machineWordSystem raw rawLabels).Block c
        ((first + 1) + (3 * scratch + 2 * (first + 1 + gap) + 7) + (counterTime runs + 6 + 10)) finish [] ∧
      Related ⟨79, head - (first : Int) - 1 - (scratch : Int) - 1 - (counterTime runs : Int) - 6 + 10,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left), rootTail⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        ((first + 1) + (3 * scratch + 2 * (first + 1 + gap) + 7) + (counterTime runs + 6 + 10))
        (mapConfig finish) [] ∧
      0 < (first + 1) + (3 * scratch + 2 * (first + 1 + gap) + 7) + (counterTime runs + 6 + 10) := by
  have hin : Related
      ⟨state 0, head, moveLeft ⟨List.replicate first true ++ false ::
        (List.replicate scratch true ++ false ::
          (counterWord runs ++ List.replicate 6 false ++ false :: left)),
        false :: (List.replicate gap false ++ true :: false :: tail)⟩ false⟩ c := by
    simpa [state] using hrel
  obtain ⟨mid, hp, hr, hq, _⟩ := physical_cross_zero 0 first head
    (List.replicate scratch true ++ false :: (counterWord runs ++ List.replicate 6 false ++ false :: left))
    (List.replicate gap false ++ true :: false :: tail) false c hin
  have hz : List.replicate first false ++ false :: (List.replicate gap false ++ true :: false :: tail) =
      List.replicate (first + 1 + gap) false ++ true :: false :: tail := by
    calc
      _ = (List.replicate first false ++ List.replicate 1 false ++ List.replicate gap false) ++
          true :: false :: tail := by simp [List.append_assoc]
      _ = _ := by rw [List.replicate_append_replicate, List.replicate_append_replicate]
  have hr' : Related
      ⟨68, head - (first : Int) - 1, moveLeft
        ⟨List.replicate scratch true ++ false :: (counterWord runs ++ List.replicate 6 false ++ false :: left),
          false :: (List.replicate (first + 1 + gap) false ++ true :: false :: tail)⟩ false⟩ mid := by
    simpa [destination, hz] using hr
  obtain ⟨mid2, hp2, hr2, hq2, _⟩ := physical_cleanup_zero_anchor scratch (first + 1 + gap)
    (head - (first : Int) - 1) (counterWord runs ++ List.replicate 6 false ++ false :: left) tail mid hr'
  obtain ⟨finish, hp3, hr3, hq3, _⟩ := Continue.counter_to_root runs bit rootTail
    (head - (first : Int) - 1 - (scratch : Int) - 1) left
    (List.replicate (scratch + 1 + (first + 1 + gap)) false ++ true :: false :: tail) mid2 hroot hr2
  have hphys := (hp.trans (machineWordSystem raw rawLabels) hp2).trans (machineWordSystem raw rawLabels) hp3
  have hquot := (hq.trans (machineWordSystem machine machineLabels) hq2).trans (machineWordSystem machine machineLabels) hq3
  exact ⟨finish, by simpa using hphys, hr3, by simpa using hquot, by omega⟩
private theorem zeros_join (a b : Nat) (tail : List Bool) :
    List.replicate a false ++ false :: (List.replicate b false ++ tail) =
      List.replicate (a + 1 + b) false ++ tail := by
  calc
    _ = (List.replicate a false ++ List.replicate 1 false ++ List.replicate b false) ++ tail := by
      simp [List.append_assoc]
    _ = _ := by rw [List.replicate_append_replicate, List.replicate_append_replicate]

/-- A prepared three-marker break, generalized cleanup and counter return
reach the root silently under the displayed finite control-prefix condition. -/
theorem physical_three_to_root (first second third scratch gap : Nat) (runs : List (Fin 6))
    (bit : Bool) (rootTail : List Bool) (head : Int) (left tail : List Bool) (c : Config 237)
    (hroot : counterPush runs
      (List.replicate (scratch + 1 + (third + 1 + (second + 1 + (first + 1 + gap)))) false ++
        true :: false :: tail) = true :: bit :: rootTail)
    (hrel : Related
      ⟨71, head, moveLeft ⟨List.replicate first true ++ false ::
        (List.replicate second true ++ false :: (List.replicate third true ++ false ::
          (List.replicate scratch true ++ false ::
            (counterWord runs ++ List.replicate 6 false ++ false :: left)))),
        false :: (List.replicate gap false ++ true :: false :: tail)⟩ false⟩ c) :
    ∃ finish, (machineWordSystem raw rawLabels).Block c
        (((first + 1) + ((second + 1) + (third + 1))) +
          (3 * scratch + 2 * (third + 1 + (second + 1 + (first + 1 + gap))) + 7) +
          (counterTime runs + 6 + 10)) finish [] ∧
      Related ⟨79, head - (first : Int) - 1 - (second : Int) - 1 - (third : Int) - 1 -
        (scratch : Int) - 1 - (counterTime runs : Int) - 6 + 10,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left), rootTail⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (((first + 1) + ((second + 1) + (third + 1))) +
          (3 * scratch + 2 * (third + 1 + (second + 1 + (first + 1 + gap))) + 7) +
          (counterTime runs + 6 + 10)) (mapConfig finish) [] ∧
      0 < ((first + 1) + ((second + 1) + (third + 1))) +
          (3 * scratch + 2 * (third + 1 + (second + 1 + (first + 1 + gap))) + 7) +
          (counterTime runs + 6 + 10) := by
  have hb := cross_three first second third head
    (List.replicate scratch true ++ false :: (counterWord runs ++ List.replicate 6 false ++ false :: left))
    (List.replicate gap false ++ true :: false :: tail) false
  obtain ⟨mid, hp, hr, hq⟩ := Continue.physical_silent_block _ _ _ hb c hrel
  let gap' := third + 1 + (second + 1 + (first + 1 + gap))
  have hz : List.replicate third false ++ false :: (List.replicate second false ++ false ::
      (List.replicate first false ++ false :: (List.replicate gap false ++ true :: false :: tail))) =
      List.replicate gap' false ++ true :: false :: tail := by
    dsimp [gap']
    rw [zeros_join first gap, zeros_join second (first + 1 + gap),
      zeros_join third (second + 1 + (first + 1 + gap))]
  have hr' : Related
      ⟨68, head - (first : Int) - 1 - (second : Int) - 1 - (third : Int) - 1, moveLeft
        ⟨List.replicate scratch true ++ false :: (counterWord runs ++ List.replicate 6 false ++ false :: left),
          false :: (List.replicate gap' false ++ true :: false :: tail)⟩ false⟩ mid := by
    simpa [hz] using hr
  obtain ⟨mid2, hp2, hr2, hq2, _⟩ := physical_cleanup_zero_anchor scratch gap'
    (head - (first : Int) - 1 - (second : Int) - 1 - (third : Int) - 1)
    (counterWord runs ++ List.replicate 6 false ++ false :: left) tail mid hr'
  obtain ⟨finish, hp3, hr3, hq3, _⟩ := Continue.counter_to_root runs bit rootTail
    (head - (first : Int) - 1 - (second : Int) - 1 - (third : Int) - 1 - (scratch : Int) - 1) left
    (List.replicate (scratch + 1 + gap') false ++ true :: false :: tail) mid2 hroot hr2
  have hphys := (hp.trans (machineWordSystem raw rawLabels) hp2).trans (machineWordSystem raw rawLabels) hp3
  have hquot := (hq.trans (machineWordSystem machine machineLabels) hq2).trans (machineWordSystem machine machineLabels) hq3
  exact ⟨finish, by simpa [gap'] using hphys, hr3, by simpa [gap'] using hquot, by omega⟩
/-- Positive and negative finite controls for a literal break scan. -/
example : rawSystem.Block ⟨69, 0, ⟨[false], [true]⟩⟩ 2
    ⟨68, -2, ⟨[], [false, false, false]⟩⟩ [] := by
  constructor <;> decide

example : ¬ rawSystem.Block ⟨69, 0, ⟨[false], [true]⟩⟩ 1
    ⟨68, -2, ⟨[], [false, false, false]⟩⟩ [] := by
  intro h
  have bad : rawSystem.advance ⟨69, 0, ⟨[false], [true]⟩⟩ 1 ≠
      ⟨68, -2, ⟨[], [false, false, false]⟩⟩ := by decide
  exact bad h.endpoint
end PASoundness.M236.Break
