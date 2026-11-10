import PASoundness.M236Control
/-! Path-successor factorizations of the literal physical return control. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

/-- Replace the last zero in a path by one and discard its trailing ones. -/
def successorPath (path : List Bool) : Option (List Bool) := do
  let (_, rest) ← pop path.reverse
  pure (rest.reverse ++ [true])

/-- Skip the last zero, replace the preceding zero by one, and discard the
suffix. The caller must prove this stays inside the source sentinel. -/
def skipSuccessorPath (path : List Bool) : Option (List Bool) := do
  let (_, rest1) ← pop path.reverse
  let (_, rest2) ← pop rest1
  pure (rest2.reverse ++ [true])

/-- The first two root bits are checked; the third is retained for the
runtime and the remaining bits are the path read by state 79. -/
def parseRoot (path : List Bool) : Option (Bool × List Bool) :=
  match path with
  | true :: true :: bit :: tail => some (bit, tail)
  | _ => none

theorem decodeOne_successor (word : List Bool) :
    decodeOne word = (successorPath ([true, true, false] ++ word)).bind parseRoot := by
  unfold decodeOne successorPath parseRoot
  cases h : pop ([true, true, false] ++ word).reverse with
  | none => rfl
  | some x => cases x; rfl

theorem decodeZero_successor (word : List Bool) :
    decodeZero word = (skipSuccessorPath ([true, true, false] ++ word)).bind parseRoot := by
  unfold decodeZero skipSuccessorPath parseRoot
  cases h : pop ([true, true, false] ++ word).reverse with
  | none => rfl
  | some x =>
    cases x with
    | mk count rest =>
      cases h2 : pop rest with
      | none => simp [h2]
      | some y => cases y; simp [h2] <;> rfl

/-- Whenever a path factors at its last zero, `successorPath` performs exactly
that conventional successor transformation. -/
theorem successorPath_factor (pcPrefix : List Bool) (scratch : Nat) :
    successorPath (pcPrefix ++ false :: List.replicate scratch true) = some (pcPrefix ++ [true]) := by
  unfold successorPath
  simp only [List.reverse_append, List.reverse_cons, List.reverse_replicate, List.append_assoc, List.cons_append, List.nil_append]
  rw [pop_run]
  simp

/-- The two-zero version implements the same transformation after skipping
the last zero, retaining both discarded one-runs only in the hypothesis. -/
theorem skipSuccessorPath_factor (pcPrefix : List Bool) (scratch1 scratch2 : Nat) :
    skipSuccessorPath (pcPrefix ++ false :: (List.replicate scratch2 true ++ false :: List.replicate scratch1 true)) =
      some (pcPrefix ++ [true]) := by
  unfold skipSuccessorPath
  simp only [List.reverse_append, List.reverse_cons, List.reverse_replicate, List.append_assoc, List.cons_append, List.nil_append]
  rw [pop_run]
  simp [pop_run]

/-- Successful root parsing determines every bit of its input. -/
theorem parseRoot_some {path : List Bool} {bit : Bool} {tail : List Bool}
    (h : parseRoot path = some (bit, tail)) : path = [true, true, bit] ++ tail := by
  cases path with
  | nil => simp [parseRoot] at h
  | cons a xs =>
    cases a with
    | false => simp [parseRoot] at h
    | true =>
      cases xs with
      | nil => simp [parseRoot] at h
      | cons b ys =>
        cases b with
        | false => simp [parseRoot] at h
        | true =>
          cases ys with
          | nil => simp [parseRoot] at h
          | cons c zs =>
            simp [parseRoot] at h
            rcases h with ⟨rfl, rfl⟩
            rfl

theorem successor_of_decodeOne (word : List Bool) (bit : Bool) (pcTail : List Bool)
    (h : decodeOne word = some (bit, pcTail)) :
    successorPath ([true, true, false] ++ word) = some ([true, true, bit] ++ pcTail) := by
  rw [decodeOne_successor] at h
  change (successorPath ([true, true, false] ++ word)).bind parseRoot = some (bit, pcTail) at h
  cases hs : successorPath ([true, true, false] ++ word) with
  | none =>
    simp only [List.cons_append, List.nil_append] at hs
    simp [hs] at h
  | some path =>
    simp only [List.cons_append, List.nil_append] at hs
    have hp : parseRoot path = some (bit, pcTail) := by simpa [hs] using h
    rw [parseRoot_some hp]

theorem successor_of_decodeZero (word : List Bool) (bit : Bool) (pcTail : List Bool)
    (h : decodeZero word = some (bit, pcTail)) :
    skipSuccessorPath ([true, true, false] ++ word) = some ([true, true, bit] ++ pcTail) := by
  rw [decodeZero_successor] at h
  change (skipSuccessorPath ([true, true, false] ++ word)).bind parseRoot = some (bit, pcTail) at h
  cases hs : skipSuccessorPath ([true, true, false] ++ word) with
  | none =>
    simp only [List.cons_append, List.nil_append] at hs
    simp [hs] at h
  | some path =>
    simp only [List.cons_append, List.nil_append] at hs
    have hp : parseRoot path = some (bit, pcTail) := by simpa [hs] using h
    rw [parseRoot_some hp]

theorem physical_root_zero_successor (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (hzero : registers r = 0) (reserve : List Nat) (gap : Nat) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none))
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: false ::
          Redispatch.selectedPayload registers r reserve tail)⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (scratch1 scratch2 : Nat) (bit : Bool)
      (pcTail : List Bool) (finish : Config 237),
      skipSuccessorPath ([true, true, false] ++ word) = some ([true, true, bit] ++ pcTail) ∧ 0 < time ∧
      (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          pcTail ++ (List.replicate (gap + (scratch2 + scratch1 + 3)) false ++ true :: false ::
            (bank (UnaryNine.values registers ++ reserve) ++ false :: tail))⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] ∧
      UnaryCodec.decodeBank (9 + reserve.length) (bank (UnaryNine.values registers ++ reserve) ++ false :: tail) =
        some (UnaryNine.values registers ++ reserve, false :: tail) ∧
      RegisterMachine.execute (.decNZ r) registers = ⟨registers, false, []⟩ := by
  obtain ⟨time, endHead, scratch1, scratch2, bit, pcTail, finish, hdec, ht, hp, hr, hq, hd, hout⟩ := physical_root_zero_decoded registers r hzero reserve gap word write hpath head left tail c hrel
  exact ⟨time, endHead, scratch1, scratch2, bit, pcTail, finish, successor_of_decodeZero word bit pcTail hdec, ht, hp, hr, hq, hd, hout⟩

theorem physical_root_positive_successor (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (value : Nat) (hvalue : registers r = value + 1) (reserve : List Nat) (gap : Nat)
    (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none))
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: false ::
          Redispatch.selectedPayload registers r reserve tail)⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (scratch : Nat) (bit : Bool) (pcTail : List Bool) (finish : Config 237),
      successorPath ([true, true, false] ++ word) = some ([true, true, bit] ++ pcTail) ∧ 0 < time ∧
      (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          pcTail ++ (List.replicate (gap + scratch + 2) false ++ true :: false ::
            (bank (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0])) ++ tail))⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] ∧
      UnaryCodec.decodeBank (9 + (reserve ++ [0]).length)
        (bank (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0])) ++ tail) =
        some (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0]), tail) ∧
      RegisterMachine.execute (.decNZ r) registers = ⟨RegisterMachine.write registers r value, true, []⟩ := by
  obtain ⟨time, endHead, scratch, bit, pcTail, finish, hdec, ht, hp, hr, hq, hd, hout⟩ := physical_root_positive_decoded registers r value hvalue reserve gap word write hpath head left tail c hrel
  exact ⟨time, endHead, scratch, bit, pcTail, finish, successor_of_decodeOne word bit pcTail hdec, ht, hp, hr, hq, hd, hout⟩

theorem physical_root_increment_successor (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (reserve : List Nat) (gap : Nat) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".inc") (Selector.entryState r) write .right none))
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: false ::
          Redispatch.selectedPayload registers r reserve tail)⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (scratch : Nat) (bit : Bool) (pcTail : List Bool) (finish : Config 237),
      successorPath ([true, true, false] ++ word) = some ([true, true, bit] ++ pcTail) ∧ 0 < time ∧
      (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          pcTail ++ (List.replicate (gap + scratch + 2) false ++ true :: false ::
            (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail))⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] ∧
      UnaryCodec.decodeBank (9 + reserve.length)
        (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail) =
        some (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve, tail) := by
  obtain ⟨time, endHead, scratch, bit, pcTail, finish, hdec, ht, hp, hr, hq, hd⟩ := physical_root_increment_decoded registers r reserve gap word write hpath head left tail c hrel
  exact ⟨time, endHead, scratch, bit, pcTail, finish, successor_of_decodeOne word bit pcTail hdec, ht, hp, hr, hq, hd⟩


example : successorPath [true, true, false, false, true, true] =
    some [true, true, false, true] := by decide
example : skipSuccessorPath [true, true, false, false, true, true] =
    some [true, true, true] := by decide
example : successorPath [true, true, false, false, true, true] ≠
    some [true, true, true] := by decide
end PASoundness.M236.Control
