import PASoundness.M236UnaryCleanup

/-! Literal restoration of the one-cell bank anchor and entry to the
leftward return counter. The prepared entry layout is an explicit hypothesis;
this module does not assert its reachability or source-control correspondence. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.UnaryAnchor
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift

private theorem replicate_shift (b : Bool) (n : Nat) (tail : List Bool) :
    List.replicate n b ++ (b :: tail) = b :: (List.replicate n b ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

/-- Raw state 72 scans zeros leftward without changing the tape. -/
theorem scan_zeros (count : Nat) (head : Int) (left right : List Bool) :
    rawSystem.Block ⟨72, head, ⟨List.replicate count false ++ left, false :: right⟩⟩ count
      ⟨72, head - (count : Int), ⟨left, false :: (List.replicate count false ++ right)⟩⟩ [] := by
  induction count generalizing head right with
  | zero => simpa using WordEventSystem.Block.refl rawSystem ⟨72, head, ⟨left, false :: right⟩⟩
  | succ count ih =>
    have row : raw.table.row 72 false = ⟨false, .left, 72, false⟩ := by decide
    have ev : rawLabels.at 72 false = none := by decide
    have hs : rawSystem.step
        ⟨72, head, ⟨List.replicate (count + 1) false ++ left, false :: right⟩⟩ =
        (⟨72, head - 1, ⟨List.replicate count false ++ left, false :: false :: right⟩⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row, ev,
        Move.apply, moveLeft, List.replicate_succ]
    have hb := (WordEventSystem.Block.single rawSystem hs).trans rawSystem
      (ih (head - 1) (false :: right))
    have hh : head - 1 - (count : Int) = head - ((count + 1 : Nat) : Int) := by omega
    simpa only [List.nil_append, hh, Nat.add_comm 1 count, List.replicate_succ,
      List.cons_append, replicate_shift] using hb

/-- From the one-zero anchor position, restore its one, traverse the finite
zero gap, and enter raw state 64 just to the left of the preserved marker. -/
theorem restore_and_scan (count : Nat) (head : Int) (left right : List Bool) :
    rawSystem.Block
      ⟨1, head, ⟨List.replicate count false ++ true :: left, false :: right⟩⟩
      (count + 2)
      ⟨64, head - (count : Int) - 2,
        moveLeft ⟨left, true :: (List.replicate count false ++ true :: right)⟩ true⟩ [] := by
  have row0 : raw.table.row 1 false = ⟨true, .left, 72, false⟩ := by decide
  have ev0 : rawLabels.at 1 false = none := by decide
  have row1 : raw.table.row 72 true = ⟨true, .left, 64, false⟩ := by decide
  have ev1 : rawLabels.at 72 true = none := by decide
  have hs0 : rawSystem.step
      ⟨1, head, ⟨List.replicate count false ++ true :: left, false :: right⟩⟩ =
      (⟨72, head - 1, moveLeft ⟨List.replicate count false ++ true :: left, false :: right⟩ true⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row0, ev0,
      Move.apply]
  cases count with
  | zero =>
    have hs1 : rawSystem.step ⟨72, head - 1, ⟨left, true :: true :: right⟩⟩ =
        (⟨64, head - 2, moveLeft ⟨left, true :: true :: right⟩ true⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row1, ev1,
        Move.apply]
      omega
    have hb := (WordEventSystem.Block.single rawSystem hs0).trans rawSystem
      (WordEventSystem.Block.single rawSystem hs1)
    simpa [moveLeft] using hb
  | succ count =>
    have hscan := scan_zeros count (head - 1) (true :: left) (true :: right)
    have rowz : raw.table.row 72 false = ⟨false, .left, 72, false⟩ := by decide
    have evz : rawLabels.at 72 false = none := by decide
    have hsz : rawSystem.step
        ⟨72, head - 1 - (count : Int),
          ⟨true :: left, false :: (List.replicate count false ++ true :: right)⟩⟩ =
        (⟨72, head - 1 - (count : Int) - 1,
          ⟨left, true :: false :: (List.replicate count false ++ true :: right)⟩⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, rowz, evz,
        Move.apply, moveLeft]
    have hs1 : rawSystem.step
        ⟨72, head - 1 - (count : Int) - 1,
          ⟨left, true :: false :: (List.replicate count false ++ true :: right)⟩⟩ =
        (⟨64, head - 1 - (count : Int) - 2,
          moveLeft ⟨left, true :: false :: (List.replicate count false ++ true :: right)⟩ true⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row1, ev1,
        Move.apply]
      omega
    have hb := (((WordEventSystem.Block.single rawSystem hs0).trans rawSystem hscan).trans rawSystem
      (WordEventSystem.Block.single rawSystem hsz)).trans rawSystem (WordEventSystem.Block.single rawSystem hs1)
    have hh : head - 1 - (count : Int) - 2 = head - (((count + 1) : Nat) : Int) - 2 := by omega
    have ht : 1 + count + 1 + 1 = (count + 1) + 2 := by omega
    simpa only [moveLeft, List.replicate_succ, List.cons_append, List.drop_succ_cons,
      List.drop_zero, List.headD_cons, List.nil_append, hh, ht] using hb

/-- A one-cell anchor is erased and then restored; every unary bank block
beyond its separator and all outer data are preserved. -/
theorem anchor_cleanup (scratch : Nat) (values : List Nat) (head : Int)
    (left tail : List Bool) :
    rawSystem.Block
      ⟨68, head, moveLeft ⟨List.replicate scratch true ++ false :: left,
        false :: false :: (bank (0 :: values) ++ tail)⟩ false⟩
      (3 * scratch + 9)
      ⟨64, head - (scratch : Int) - 1,
        moveLeft ⟨left, true :: (List.replicate (scratch + 2) false ++
          true :: false :: (bank values ++ tail))⟩ true⟩ [] := by
  have hraw := UnaryCleanup.cleanup_block scratch 0 values head left tail
  have hfirst : rawSystem.Block
      ⟨68, head, moveLeft ⟨List.replicate scratch true ++ false :: left,
        false :: false :: (bank (0 :: values) ++ tail)⟩ false⟩
      (2 * scratch + 5)
      ⟨1, head + 3, ⟨List.replicate (scratch + 2) false ++ true :: left,
        false :: false :: (bank values ++ tail)⟩⟩ [] := by
    simpa [moveLeft] using hraw
  have hrest := restore_and_scan (scratch + 2) (head + 3) left
    (false :: (bank values ++ tail))
  have hb := hfirst.trans rawSystem hrest
  have ht : 2 * scratch + 5 + ((scratch + 2) + 2) = 3 * scratch + 9 := by omega
  have hh : head + 3 - ((scratch + 2 : Nat) : Int) - 2 = head - (scratch : Int) - 1 := by omega
  simpa only [List.nil_append, ht, hh] using hb

/-- The anchored return block is valid for the full raw and quotient tapes. -/
theorem physical_anchor_cleanup (scratch : Nat) (values : List Nat) (head : Int)
    (left tail : List Bool) (c : Config 237)
    (hrel : Related
      ⟨68, head, moveLeft ⟨List.replicate scratch true ++ false :: left,
        false :: false :: (bank (0 :: values) ++ tail)⟩ false⟩ c) :
    ∃ finish,
      (machineWordSystem raw rawLabels).Block c (3 * scratch + 9) finish [] ∧
      Related
        ⟨64, head - (scratch : Int) - 1,
          moveLeft ⟨left, true :: (List.replicate (scratch + 2) false ++
            true :: false :: (bank values ++ tail))⟩ true⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (3 * scratch + 9) (mapConfig finish) [] ∧ 0 < 3 * scratch + 9 := by
  have hb := anchor_cleanup scratch values head left tail
  have hs := advance_sound raw rawLabels hrel (3 * scratch + 9)
  change Related (rawSystem.advance
      ⟨68, head, moveLeft ⟨List.replicate scratch true ++ false :: left,
        false :: false :: (bank (0 :: values) ++ tail)⟩ false⟩
      (3 * scratch + 9)) _ ∧
    rawSystem.wordFrom
      ⟨68, head, moveLeft ⟨List.replicate scratch true ++ false :: left,
        false :: false :: (bank (0 :: values) ++ tail)⟩ false⟩
      (3 * scratch + 9) = _ at hs
  rw [hb.endpoint, hb.output] at hs
  let finish := (machineWordSystem raw rawLabels).advance c (3 * scratch + 9)
  have hp : (machineWordSystem raw rawLabels).Block c (3 * scratch + 9) finish [] := ⟨rfl, hs.2.symm⟩
  exact ⟨finish, hp, hs.1, BootstrapScan.mapped_block hp, by omega⟩

/-- In the anchored nine-register layout, the actual increment and return
restore the one-cell anchor and leave the updated bank intact at state 64.
The full state-9 entry tape and finite scratch run are explicit hypotheses. -/
theorem physical_anchored_increment_nine
    (registers : RegisterMachine.Bank 9) (r : Fin 9) (reserve : List Nat)
    (scratch : Nat) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related
      ⟨9, head, ⟨(bank (0 :: UnaryIncrementNine.before registers r)).reverse ++ false :: false ::
          (List.replicate scratch true ++ false :: left),
        List.replicate (registers r + 1) true ++ false ::
          (bank (UnaryIncrementNine.after registers r ++ reserve) ++ false :: tail)⟩⟩ c) :
    ∃ first values middle finish,
      (UnaryIncrementNine.after registers r ++ reserve).reverse ++
        (registers r + 1) :: (0 :: UnaryIncrementNine.before registers r).reverse = first :: values ∧
      (machineWordSystem raw rawLabels).Block c
        (UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
          (first + 1 + (shiftTime values + 2))) middle [] ∧
      Related
        ⟨68, head + ((registers r + 2 : Nat) : Int) +
            (shiftTime (UnaryIncrementNine.after registers r ++ reserve) : Int) - 1 -
            ((first + 1 : Nat) : Int) - (shiftTime values : Int) - 2,
          moveLeft ⟨List.replicate scratch true ++ false :: left,
            false :: false :: (bank (0 ::
              (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve)) ++ tail)⟩ false⟩ middle ∧
      (machineWordSystem raw rawLabels).Block c
        (UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
          (first + 1 + (shiftTime values + 2)) + (3 * scratch + 9)) finish [] ∧
      Related
        ⟨64, head + ((registers r + 2 : Nat) : Int) +
            (shiftTime (UnaryIncrementNine.after registers r ++ reserve) : Int) - 1 -
            ((first + 1 : Nat) : Int) - (shiftTime values : Int) - 2 - (scratch : Int) - 1,
          moveLeft ⟨left, true :: (List.replicate (scratch + 2) false ++ true :: false ::
            (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail))⟩ true⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
          (first + 1 + (shiftTime values + 2)) + (3 * scratch + 9)) (mapConfig finish) [] ∧
      0 < UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
        (first + 1 + (shiftTime values + 2)) + (3 * scratch + 9) ∧
      UnaryCodec.decodeBank (9 + reserve.length)
        (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail) =
        some (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve, tail) := by
  obtain ⟨first, values, middle, he, hp, hr, hq, ht, _⟩ :=
    UnaryReturn.physical_increment_return (0 :: UnaryIncrementNine.before registers r) (registers r)
      (UnaryIncrementNine.after registers r ++ reserve) head
      (List.replicate scratch true ++ false :: left) tail c hrel
  have hvalues : (0 :: UnaryIncrementNine.before registers r) ++ (registers r + 1) ::
        (UnaryIncrementNine.after registers r ++ reserve) =
      0 :: (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) := by
    rw [UnaryIncrementNine.values_increment]
    simp [List.append_assoc]
  rw [hvalues] at hr
  obtain ⟨finish, hp', hr', hq', _⟩ := physical_anchor_cleanup scratch
    (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve)
    (head + ((registers r + 2 : Nat) : Int) +
      (shiftTime (UnaryIncrementNine.after registers r ++ reserve) : Int) - 1 -
      ((first + 1 : Nat) : Int) - (shiftTime values : Int) - 2) left tail middle hr
  refine ⟨first, values, middle, finish, he, hp, hr, ?_, hr', ?_, by omega, ?_⟩
  · simpa using hp.trans (machineWordSystem raw rawLabels) hp'
  · simpa using hq.trans (machineWordSystem machine machineLabels) hq'
  · simpa only [List.length_append, UnaryNine.values_length] using
      UnaryCodec.decode_bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) tail

/-- A finite zero run of length at most five followed by one resets the
return counter without altering the scanned cells. -/
theorem counter_segment (zeros : Fin 6) (head : Int) (left right : List Bool) :
    rawSystem.Block
      ⟨64, head, moveLeft ⟨List.replicate zeros.val false ++ true :: left, true :: right⟩ true⟩
      (zeros.val + 1)
      ⟨64, head - ((zeros.val + 1 : Nat) : Int),
        moveLeft ⟨left, true :: (List.replicate zeros.val false ++ true :: right)⟩ true⟩ [] := by
  have r59o : raw.table.row 59 true = ⟨true, .left, 64, false⟩ := by decide
  have e59o : rawLabels.at 59 true = none := by decide
  have r60z : raw.table.row 60 false = ⟨false, .left, 59, false⟩ := by decide
  have r60o : raw.table.row 60 true = ⟨true, .left, 64, false⟩ := by decide
  have e60z : rawLabels.at 60 false = none := by decide
  have e60o : rawLabels.at 60 true = none := by decide
  have r61z : raw.table.row 61 false = ⟨false, .left, 60, false⟩ := by decide
  have r61o : raw.table.row 61 true = ⟨true, .left, 64, false⟩ := by decide
  have e61z : rawLabels.at 61 false = none := by decide
  have e61o : rawLabels.at 61 true = none := by decide
  have r62z : raw.table.row 62 false = ⟨false, .left, 61, false⟩ := by decide
  have r62o : raw.table.row 62 true = ⟨true, .left, 64, false⟩ := by decide
  have e62z : rawLabels.at 62 false = none := by decide
  have e62o : rawLabels.at 62 true = none := by decide
  have r63z : raw.table.row 63 false = ⟨false, .left, 62, false⟩ := by decide
  have r63o : raw.table.row 63 true = ⟨true, .left, 64, false⟩ := by decide
  have e63z : rawLabels.at 63 false = none := by decide
  have e63o : rawLabels.at 63 true = none := by decide
  have r64z : raw.table.row 64 false = ⟨false, .left, 63, false⟩ := by decide
  have r64o : raw.table.row 64 true = ⟨true, .left, 64, false⟩ := by decide
  have e64z : rawLabels.at 64 false = none := by decide
  have e64o : rawLabels.at 64 true = none := by decide
  have he : zeros.val = 0 ∨ zeros.val = 1 ∨ zeros.val = 2 ∨ zeros.val = 3 ∨ zeros.val = 4 ∨ zeros.val = 5 := by
    have := zeros.isLt
    omega
  rcases he with h | h | h | h | h | h <;> simp only [h] <;> constructor <;>
    simp [WordEventSystem.advance, WordEventSystem.wordFrom, rawSystem, FiniteTape.system,
      FiniteTape.step, FiniteTape.read, moveLeft, Move.apply, r59o, e59o, r60z, r60o, e60z, e60o, r61z, r61o, e61z, e61o, r62z, r62o, e62z, e62o, r63z, r63o, e63z, e63o, r64z, r64o, e64z, e64o] <;> omega

/-- Six consecutive zeros trigger the literal transition to state 65. -/
theorem counter_stop (head : Int) (left right : List Bool) :
    rawSystem.Block
      ⟨64, head, moveLeft ⟨List.replicate 6 false ++ left, true :: right⟩ true⟩ 6
      ⟨65, head - 6, moveLeft ⟨left, false :: (List.replicate 5 false ++ true :: right)⟩ false⟩ [] := by
  have r59z : raw.table.row 59 false = ⟨false, .left, 65, false⟩ := by decide
  have e59z : rawLabels.at 59 false = none := by decide
  have r60z : raw.table.row 60 false = ⟨false, .left, 59, false⟩ := by decide
  have e60z : rawLabels.at 60 false = none := by decide
  have r61z : raw.table.row 61 false = ⟨false, .left, 60, false⟩ := by decide
  have e61z : rawLabels.at 61 false = none := by decide
  have r62z : raw.table.row 62 false = ⟨false, .left, 61, false⟩ := by decide
  have e62z : rawLabels.at 62 false = none := by decide
  have r63z : raw.table.row 63 false = ⟨false, .left, 62, false⟩ := by decide
  have e63z : rawLabels.at 63 false = none := by decide
  have r64z : raw.table.row 64 false = ⟨false, .left, 63, false⟩ := by decide
  have e64z : rawLabels.at 64 false = none := by decide
  constructor <;>
    simp [WordEventSystem.advance, WordEventSystem.wordFrom, rawSystem, FiniteTape.system,
      FiniteTape.step, FiniteTape.read, moveLeft, Move.apply, r59z, e59z, r60z, e60z,
      r61z, e61z, r62z, e62z, r63z, e63z, r64z, e64z] <;> omega

/-- A finite nearest-first word whose zero runs have length at most five.
There is no bound on the number of runs. -/
def counterWord : List (Fin 6) → List Bool
  | [] => []
  | zeros :: rest => List.replicate zeros.val false ++ true :: counterWord rest

def counterTime : List (Fin 6) → Nat
  | [] => 0
  | zeros :: rest => zeros.val + 1 + counterTime rest

def counterPush : List (Fin 6) → List Bool → List Bool
  | [], right => right
  | zeros :: rest, right =>
      counterPush rest (List.replicate zeros.val false ++ true :: right)

/-- The literal return counter traverses every finite such word without
changing any cell or emitting an event. -/
theorem counter_walk (runs : List (Fin 6)) (head : Int) (left right : List Bool) :
    rawSystem.Block
      ⟨64, head, moveLeft ⟨counterWord runs ++ left, true :: right⟩ true⟩
      (counterTime runs)
      ⟨64, head - (counterTime runs : Int),
        moveLeft ⟨left, true :: counterPush runs right⟩ true⟩ [] := by
  induction runs generalizing head right with
  | nil => simpa [counterWord, counterTime, counterPush] using
      WordEventSystem.Block.refl rawSystem ⟨64, head, moveLeft ⟨left, true :: right⟩ true⟩
  | cons zeros rest ih =>
    have hfirst := counter_segment zeros head (counterWord rest ++ left) right
    have hrest := ih (head - ((zeros.val + 1 : Nat) : Int))
      (List.replicate zeros.val false ++ true :: right)
    have hb := hfirst.trans rawSystem hrest
    have hh : head - ((zeros.val + 1 : Nat) : Int) - (counterTime rest : Int) =
        head - ((zeros.val + 1 + counterTime rest : Nat) : Int) := by omega
    simpa only [counterWord, counterTime, counterPush, List.nil_append, List.cons_append,
      List.append_assoc, hh] using hb

/-- Any finite sequence of permitted zero runs followed by six zeros reaches
state 65 in finite time; the complete zipper and event word are retained. -/
theorem counter_walk_stop (runs : List (Fin 6)) (head : Int) (left right : List Bool) :
    rawSystem.Block
      ⟨64, head, moveLeft ⟨counterWord runs ++ List.replicate 6 false ++ left, true :: right⟩ true⟩
      (counterTime runs + 6)
      ⟨65, head - (counterTime runs : Int) - 6,
        moveLeft ⟨left, false :: (List.replicate 5 false ++ true :: counterPush runs right)⟩ false⟩ [] := by
  have hb := counter_walk runs head (List.replicate 6 false ++ left) right
  have hs := counter_stop (head - (counterTime runs : Int)) left (counterPush runs right)
  simpa only [List.nil_append, List.append_assoc] using hb.trans rawSystem hs

/-- The counter block refines both complete two-way-tape machines. -/
theorem physical_counter (runs : List (Fin 6)) (head : Int) (left right : List Bool)
    (c : Config 237)
    (hrel : Related
      ⟨64, head, moveLeft ⟨counterWord runs ++ List.replicate 6 false ++ left, true :: right⟩ true⟩ c) :
    ∃ finish,
      (machineWordSystem raw rawLabels).Block c (counterTime runs + 6) finish [] ∧
      Related ⟨65, head - (counterTime runs : Int) - 6,
        moveLeft ⟨left, false :: (List.replicate 5 false ++ true :: counterPush runs right)⟩ false⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (counterTime runs + 6) (mapConfig finish) [] ∧ 0 < counterTime runs + 6 := by
  have hb := counter_walk_stop runs head left right
  have hs := advance_sound raw rawLabels hrel (counterTime runs + 6)
  change Related (rawSystem.advance
      ⟨64, head, moveLeft ⟨counterWord runs ++ List.replicate 6 false ++ left, true :: right⟩ true⟩
      (counterTime runs + 6)) _ ∧
    rawSystem.wordFrom
      ⟨64, head, moveLeft ⟨counterWord runs ++ List.replicate 6 false ++ left, true :: right⟩ true⟩
      (counterTime runs + 6) = _ at hs
  rw [hb.endpoint, hb.output] at hs
  let finish := (machineWordSystem raw rawLabels).advance c (counterTime runs + 6)
  have hp : (machineWordSystem raw rawLabels).Block c (counterTime runs + 6) finish [] := ⟨rfl, hs.2.symm⟩
  exact ⟨finish, hp, hs.1, BootstrapScan.mapped_block hp, by omega⟩

/-- Anchored nine-register increment through the unbounded return counter.
The run-word and six-zero root boundary are explicit physical preconditions;
no source grammar reachability is assumed. -/
theorem physical_anchored_increment_counter_nine
    (registers : RegisterMachine.Bank 9) (r : Fin 9) (reserve : List Nat)
    (scratch : Nat) (runs : List (Fin 6)) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related
      ⟨9, head, ⟨(bank (0 :: UnaryIncrementNine.before registers r)).reverse ++ false :: false ::
          (List.replicate scratch true ++ false :: (counterWord runs ++ List.replicate 6 false ++ left)),
        List.replicate (registers r + 1) true ++ false ::
          (bank (UnaryIncrementNine.after registers r ++ reserve) ++ false :: tail)⟩⟩ c) :
    ∃ first values middle finish,
      (UnaryIncrementNine.after registers r ++ reserve).reverse ++
        (registers r + 1) :: (0 :: UnaryIncrementNine.before registers r).reverse = first :: values ∧
      (machineWordSystem raw rawLabels).Block c
        (UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
          (first + 1 + (shiftTime values + 2)) + (3 * scratch + 9)) middle [] ∧
      (machineWordSystem raw rawLabels).Block c
        (UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
          (first + 1 + (shiftTime values + 2)) + (3 * scratch + 9) + (counterTime runs + 6)) finish [] ∧
      Related
        ⟨65, head + ((registers r + 2 : Nat) : Int) +
            (shiftTime (UnaryIncrementNine.after registers r ++ reserve) : Int) - 1 -
            ((first + 1 : Nat) : Int) - (shiftTime values : Int) - 2 - (scratch : Int) - 1 -
            (counterTime runs : Int) - 6,
          moveLeft ⟨left, false :: (List.replicate 5 false ++ true ::
            counterPush runs (List.replicate (scratch + 2) false ++ true :: false ::
              (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail)))⟩ false⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
          (first + 1 + (shiftTime values + 2)) + (3 * scratch + 9) + (counterTime runs + 6))
        (mapConfig finish) [] ∧
      0 < UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
        (first + 1 + (shiftTime values + 2)) + (3 * scratch + 9) + (counterTime runs + 6) ∧
      UnaryCodec.decodeBank (9 + reserve.length)
        (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail) =
        some (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve, tail) := by
  obtain ⟨first, values, _, middle, he, _, _, hp, hr, hq, ht, hd⟩ :=
    physical_anchored_increment_nine registers r reserve scratch head
      (counterWord runs ++ List.replicate 6 false ++ left) tail c hrel
  obtain ⟨finish, hp', hr', hq', _⟩ := physical_counter runs
    (head + ((registers r + 2 : Nat) : Int) +
      (shiftTime (UnaryIncrementNine.after registers r ++ reserve) : Int) - 1 -
      ((first + 1 : Nat) : Int) - (shiftTime values : Int) - 2 - (scratch : Int) - 1) left
    (List.replicate (scratch + 2) false ++ true :: false ::
      (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail)) middle hr
  refine ⟨first, values, middle, finish, he, hp, ?_, hr', ?_, by omega, hd⟩
  · simpa using hp.trans (machineWordSystem raw rawLabels) hp'
  · simpa using hq.trans (machineWordSystem machine machineLabels) hq'

/-- State 65 moves right over an arbitrary finite zero prefix. -/
theorem root_scan_zeros (count : Nat) (head : Int) (left tail : List Bool) :
    rawSystem.Block ⟨65, head, ⟨left, List.replicate count false ++ true :: tail⟩⟩ count
      ⟨65, head + (count : Int), ⟨List.replicate count false ++ left, true :: tail⟩⟩ [] := by
  induction count generalizing head left with
  | zero => simpa using WordEventSystem.Block.refl rawSystem ⟨65, head, ⟨left, true :: tail⟩⟩
  | succ count ih =>
    have row : raw.table.row 65 false = ⟨false, .right, 65, false⟩ := by decide
    have ev : rawLabels.at 65 false = none := by decide
    have hs : rawSystem.step
        ⟨65, head, ⟨left, List.replicate (count + 1) false ++ true :: tail⟩⟩ =
        (⟨65, head + 1, ⟨false :: left, List.replicate count false ++ true :: tail⟩⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row, ev,
        Move.apply, moveRight, List.replicate_succ]
    have hb := (WordEventSystem.Block.single rawSystem hs).trans rawSystem
      (ih (head + 1) (false :: left))
    have hh : head + 1 + (count : Int) = head + ((count + 1 : Nat) : Int) := by omega
    simpa only [List.nil_append, hh, Nat.add_comm 1 count, List.replicate_succ,
      List.cons_append, replicate_shift] using hb

/-- Under the literal two-one root prefix, the scan enters raw state 79.
The third bit is cleared exactly as the table specifies. -/
theorem root_reentry (count : Nat) (bit : Bool) (head : Int) (left tail : List Bool) :
    rawSystem.Block
      ⟨65, head, ⟨left, List.replicate count false ++ true :: true :: bit :: tail⟩⟩
      (count + 3)
      ⟨79, head + (count : Int) + 3,
        ⟨false :: true :: true :: (List.replicate count false ++ left), tail⟩⟩ [] := by
  have hscan := root_scan_zeros count head left (true :: bit :: tail)
  have r65 : raw.table.row 65 true = ⟨true, .right, 66, false⟩ := by decide
  have e65 : rawLabels.at 65 true = none := by decide
  have r66 : raw.table.row 66 true = ⟨true, .right, 67, false⟩ := by decide
  have e66 : rawLabels.at 66 true = none := by decide
  have r67z : raw.table.row 67 false = ⟨false, .right, 79, false⟩ := by decide
  have r67o : raw.table.row 67 true = ⟨false, .right, 79, false⟩ := by decide
  have e67z : rawLabels.at 67 false = none := by decide
  have e67o : rawLabels.at 67 true = none := by decide
  have hs : rawSystem.Block
      ⟨65, head + (count : Int), ⟨List.replicate count false ++ left, true :: true :: bit :: tail⟩⟩ 3
      ⟨79, head + (count : Int) + 3,
        ⟨false :: true :: true :: (List.replicate count false ++ left), tail⟩⟩ [] := by
    cases bit <;> constructor <;>
      simp [WordEventSystem.advance, WordEventSystem.wordFrom, rawSystem, FiniteTape.system,
        FiniteTape.step, FiniteTape.read, moveRight, Move.apply, r65, e65, r66, e66,
        r67z, r67o, e67z, e67o] <;> omega
  simpa only [List.nil_append] using hscan.trans rawSystem hs

/-- Full anchored physical increment to literal raw state 79, for a displayed
root prefix. The producer metadata names that state `main().0`; no source
occurrence correspondence or global reachability is assumed. -/
theorem physical_anchored_increment_root_nine
    (registers : RegisterMachine.Bank 9) (r : Fin 9) (reserve : List Nat)
    (scratch : Nat) (runs : List (Fin 6)) (bit : Bool) (rootTail : List Bool)
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hroot : counterPush runs (List.replicate (scratch + 2) false ++ true :: false ::
        (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail)) =
      true :: bit :: rootTail)
    (hrel : Related
      ⟨9, head, ⟨(bank (0 :: UnaryIncrementNine.before registers r)).reverse ++ false :: false ::
          (List.replicate scratch true ++ false :: (counterWord runs ++ List.replicate 6 false ++ false :: left)),
        List.replicate (registers r + 1) true ++ false ::
          (bank (UnaryIncrementNine.after registers r ++ reserve) ++ false :: tail)⟩⟩ c) :
    ∃ first values middle finish,
      (UnaryIncrementNine.after registers r ++ reserve).reverse ++
        (registers r + 1) :: (0 :: UnaryIncrementNine.before registers r).reverse = first :: values ∧
      (machineWordSystem raw rawLabels).Block c
        (UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
          (first + 1 + (shiftTime values + 2)) + (3 * scratch + 9) + (counterTime runs + 6)) middle [] ∧
      (machineWordSystem raw rawLabels).Block c
        (UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
          (first + 1 + (shiftTime values + 2)) + (3 * scratch + 9) + (counterTime runs + 6) + 10) finish [] ∧
      Related
        ⟨79, head + ((registers r + 2 : Nat) : Int) +
            (shiftTime (UnaryIncrementNine.after registers r ++ reserve) : Int) - 1 -
            ((first + 1 : Nat) : Int) - (shiftTime values : Int) - 2 - (scratch : Int) - 1 -
            (counterTime runs : Int) - 6 + 10,
          ⟨false :: true :: true :: (List.replicate 7 false ++ left), rootTail⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
          (first + 1 + (shiftTime values + 2)) + (3 * scratch + 9) + (counterTime runs + 6) + 10)
        (mapConfig finish) [] ∧
      0 < UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
        (first + 1 + (shiftTime values + 2)) + (3 * scratch + 9) + (counterTime runs + 6) + 10 := by
  obtain ⟨first, values, _, middle, he, _, hp, hr, hq, ht, _⟩ :=
    physical_anchored_increment_counter_nine registers r reserve scratch runs head (false :: left) tail c hrel
  let h65 := head + ((registers r + 2 : Nat) : Int) +
      (shiftTime (UnaryIncrementNine.after registers r ++ reserve) : Int) - 1 -
      ((first + 1 : Nat) : Int) - (shiftTime values : Int) - 2 - (scratch : Int) - 1 -
      (counterTime runs : Int) - 6
  rw [hroot] at hr
  have hr0 : Related
      ⟨65, h65, ⟨left, List.replicate 7 false ++ true :: true :: bit :: rootTail⟩⟩ middle := by
    simpa [h65, moveLeft, List.replicate_succ] using hr
  have hb := root_reentry 7 bit h65 left rootTail
  obtain ⟨finish, hp', hr'⟩ := BulkSweep.physical_block raw rawLabels _ _ middle 10 hr0 hb
  have hq' := BootstrapScan.mapped_block hp'
  refine ⟨first, values, middle, finish, he, hp, ?_, ?_, ?_, by omega⟩
  · simpa using hp.trans (machineWordSystem raw rawLabels) hp'
  · simpa [h65, Int.add_assoc] using hr'
  · simpa using hq.trans (machineWordSystem machine machineLabels) hq'

/-- The return-counter transformation prepends a finite control word and is
independent of the tape suffix. -/
theorem counterPush_append (runs : List (Fin 6)) (first second : List Bool) :
    counterPush runs (first ++ second) = counterPush runs first ++ second := by
  induction runs generalizing first with
  | nil => rfl
  | cons zeros rest ih =>
    simpa only [counterPush, List.cons_append, List.append_assoc] using
      ih (List.replicate zeros.val false ++ true :: first)

/-- With a root prefix entirely inside the finite control word, the literal
increment returns to state 79 with its anchor and updated nine-register bank
still present in the exact full tape. -/
theorem physical_anchored_increment_root_bank
    (registers : RegisterMachine.Bank 9) (r : Fin 9) (reserve : List Nat)
    (scratch : Nat) (runs : List (Fin 6)) (bit : Bool) (pcTail : List Bool)
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hprefix : counterPush runs [] = true :: bit :: pcTail)
    (hrel : Related
      ⟨9, head, ⟨(bank (0 :: UnaryIncrementNine.before registers r)).reverse ++ false :: false ::
          (List.replicate scratch true ++ false :: (counterWord runs ++ List.replicate 6 false ++ false :: left)),
        List.replicate (registers r + 1) true ++ false ::
          (bank (UnaryIncrementNine.after registers r ++ reserve) ++ false :: tail)⟩⟩ c) :
    ∃ first values finish,
      (UnaryIncrementNine.after registers r ++ reserve).reverse ++
        (registers r + 1) :: (0 :: UnaryIncrementNine.before registers r).reverse = first :: values ∧
      (machineWordSystem raw rawLabels).Block c
        (UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
          (first + 1 + (shiftTime values + 2)) + (3 * scratch + 9) + (counterTime runs + 6) + 10) finish [] ∧
      Related
        ⟨79, head + ((registers r + 2 : Nat) : Int) +
            (shiftTime (UnaryIncrementNine.after registers r ++ reserve) : Int) - 1 -
            ((first + 1 : Nat) : Int) - (shiftTime values : Int) - 2 - (scratch : Int) - 1 -
            (counterTime runs : Int) - 6 + 10,
          ⟨false :: true :: true :: (List.replicate 7 false ++ left),
            pcTail ++ (List.replicate (scratch + 2) false ++ true :: false ::
              (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail))⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
          (first + 1 + (shiftTime values + 2)) + (3 * scratch + 9) + (counterTime runs + 6) + 10)
        (mapConfig finish) [] ∧
      0 < UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
        (first + 1 + (shiftTime values + 2)) + (3 * scratch + 9) + (counterTime runs + 6) + 10 ∧
      UnaryCodec.decodeBank (9 + reserve.length)
        (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail) =
        some (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve, tail) := by
  let suffix := List.replicate (scratch + 2) false ++ true :: false ::
    (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail)
  have hroot : counterPush runs suffix = true :: bit :: (pcTail ++ suffix) := by
    have h := counterPush_append runs [] suffix
    simpa [hprefix] using h
  obtain ⟨first, values, _, finish, he, _, hp, hr, hq, ht⟩ :=
    physical_anchored_increment_root_nine registers r reserve scratch runs bit (pcTail ++ suffix)
      head left tail c hroot hrel
  refine ⟨first, values, finish, he, hp, ?_, hq, ht, ?_⟩
  · simpa [suffix] using hr
  · simpa only [List.length_append, UnaryNine.values_length] using
      UnaryCodec.decode_bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) tail

example : raw.table.row 72 false ≠ ⟨false, .right, 72, false⟩ := by decide
example : raw.table.row 59 false ≠ ⟨false, .left, 64, false⟩ := by decide
example : rawLabels.at 1 false = none ∧ rawLabels.at 72 true = none ∧
    rawLabels.at 59 false = none := by decide
example : mapState 64 = 63 ∧ mapState 65 = 64 ∧ mapState 79 = 78 := by decide
example : rawSystem.Block ⟨65, 0, ⟨[], [false, false, true, true, true, false]⟩⟩ 5
    ⟨79, 5, ⟨[false, true, true, false, false], [false]⟩⟩ [] := by
  constructor <;> decide
example : ¬ rawSystem.Block ⟨65, 0, ⟨[], [false, false, true, true, true, false]⟩⟩ 4
    ⟨79, 5, ⟨[false, true, true, false, false], [false]⟩⟩ [] := by
  intro h
  have bad : rawSystem.advance ⟨65, 0, ⟨[], [false, false, true, true, true, false]⟩⟩ 4 ≠
      ⟨79, 5, ⟨[false, true, true, false, false], [false]⟩⟩ := by decide
  exact bad h.endpoint

end PASoundness.M236.UnaryAnchor
