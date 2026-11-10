import PASoundness.M236ConcreteIncrement
/-! Marked output paths on the literal table and its exact quotient. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Emit
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift

def emitName (b : Bool) : String := if b then "emit.1" else "emit.0"

/-- A named output leaf has a checked grammar path for either bit. -/
theorem emit_path_exists (b : Bool) : ∃ word : List Bool,
    Preparation.NamedPath Grammar.nodes 157 word (.leaf (emitName b) 72 true .left (some b)) := by
  cases b with
  | false =>
    refine ⟨[false, true, false, false, true, true, true, false], ?_⟩
    apply Preparation.NamedPath.step 157 141 false _ _ (by decide)
    apply Preparation.NamedPath.step 141 140 true _ _ (by decide)
    apply Preparation.NamedPath.step 140 82 false _ _ (by decide)
    apply Preparation.NamedPath.step 82 36 false _ _ (by decide)
    apply Preparation.NamedPath.step 36 25 true _ _ (by decide)
    apply Preparation.NamedPath.step 25 19 true _ _ (by decide)
    apply Preparation.NamedPath.step 19 18 true _ _ (by decide)
    exact Preparation.NamedPath.leaf 18 false _ (by decide) ⟨_, _, _, _, _, rfl⟩
  | true =>
    refine ⟨[false, true, false, false, true, true, false, true, false], ?_⟩
    apply Preparation.NamedPath.step 157 141 false _ _ (by decide)
    apply Preparation.NamedPath.step 141 140 true _ _ (by decide)
    apply Preparation.NamedPath.step 140 82 false _ _ (by decide)
    apply Preparation.NamedPath.step 82 36 false _ _ (by decide)
    apply Preparation.NamedPath.step 36 25 true _ _ (by decide)
    apply Preparation.NamedPath.step 25 19 true _ _ (by decide)
    apply Preparation.NamedPath.step 19 16 false _ _ (by decide)
    apply Preparation.NamedPath.step 16 15 true _ _ (by decide)
    exact Preparation.NamedPath.leaf 15 false _ (by decide) ⟨_, _, _, _, _, rfl⟩

/-- Any checked marked leaf path emits exactly the designated bit and has
positive physical duration, on both raw and quotient tables. -/
theorem physical_named_emit (b : Bool) (word : List Bool) (target : Fin 237)
    (write : Bool) (move : Move)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word (.leaf (emitName b) target write move (some b)))
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head, ⟨left, word ++ tail⟩⟩ c) :
    ∃ pre bit finish, word = pre ++ [bit] ∧
      (machineWordSystem raw rawLabels).Block c word.length finish [b] ∧
      Related ⟨target, move.apply (head + (pre.length : Int)),
        Grammar.finalTape pre bit write move left tail⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) word.length (mapConfig finish) [b] ∧
      0 < word.length := by
  obtain ⟨pre, bit, hw, hb⟩ := Preparation.follow_named hpath rfl head left tail
  have hroot : Grammar.nodes[(157 : Fin 158)].state = 79 := by decide
  rw [hroot] at hb
  simp only [Option.toList_some] at hb
  have ha := advance_sound raw rawLabels hrel word.length
  change Related (rawSystem.advance ⟨79, head, ⟨left, word ++ tail⟩⟩ word.length) _ ∧
    rawSystem.wordFrom ⟨79, head, ⟨left, word ++ tail⟩⟩ word.length = _ at ha
  rw [hb.endpoint, hb.output] at ha
  let finish := (machineWordSystem raw rawLabels).advance c word.length
  have hp : (machineWordSystem raw rawLabels).Block c word.length finish [b] := ⟨rfl, ha.2.symm⟩
  refine ⟨pre, bit, finish, hw, hp, ha.1, BootstrapScan.mapped_block hp, ?_⟩
  rw [hw]; simp

/-- Both event values are realized on explicit full two-way prepared tapes. -/
theorem concrete_emit (b : Bool) (head : Int) (left tail : List Bool) :
    ∃ (word pre : List Bool) (bit : Bool) (finish : Config 237),
      word = pre ++ [bit] ∧
      Preparation.NamedPath Grammar.nodes 157 word (.leaf (emitName b) 72 true .left (some b)) ∧
      (machineWordSystem raw rawLabels).Block
        (Redispatch.realizeConfig ⟨79, head, ⟨left, word ++ tail⟩⟩) word.length finish [b] ∧
      Related ⟨72, Move.left.apply (head + (pre.length : Int)),
        Grammar.finalTape pre bit true .left left tail⟩ finish ∧
      (machineWordSystem machine machineLabels).Block
        (mapConfig (Redispatch.realizeConfig ⟨79, head, ⟨left, word ++ tail⟩⟩)) word.length (mapConfig finish) [b] ∧
      0 < word.length := by
  obtain ⟨word, hpath⟩ := emit_path_exists b
  let c : Config 237 := Redispatch.realizeConfig ⟨79, head, ⟨left, word ++ tail⟩⟩
  have hrel : Related ⟨79, head, ⟨left, word ++ tail⟩⟩ c := Redispatch.realize_related _
  obtain ⟨pre, bit, finish, hw, hp, hr, hq, ht⟩ :=
    physical_named_emit b word 72 true .left hpath head left tail c hrel
  exact ⟨word, pre, bit, finish, hw, hpath, hp, hr, hq, ht⟩

example : rawSystem.Block
    ⟨79, 0, ⟨[], [false, true, false, false, true, true, true, false]⟩⟩ 8
    ⟨72, 6, Grammar.finalTape [false, true, false, false, true, true, true] false true .left [] []⟩ [false] := by
  constructor <;> decide

example : ¬ rawSystem.Block
    ⟨79, 0, ⟨[], [false, true, false, false, true, true, true, false]⟩⟩ 8
    ⟨72, 6, Grammar.finalTape [false, true, false, false, true, true, true] false true .left [] []⟩ [true] := by
  intro h
  have bad : rawSystem.wordFrom ⟨79, 0, ⟨[], [false, true, false, false, true, true, true, false]⟩⟩ 8 ≠ [true] := by decide
  exact bad h.output

example : rawSystem.Block
    ⟨79, 0, ⟨[], [false, true, false, false, true, true, false, true, false]⟩⟩ 9
    ⟨72, 7, Grammar.finalTape [false, true, false, false, true, true, false, true] false true .left [] []⟩ [true] := by
  constructor <;> decide

example : ¬ rawSystem.Block
    ⟨79, 0, ⟨[], [false, true, false, false, true, true, false, true, false]⟩⟩ 9
    ⟨72, 7, Grammar.finalTape [false, true, false, false, true, true, false, true] false true .left [] []⟩ [false] := by
  intro h
  have bad : rawSystem.wordFrom ⟨79, 0, ⟨[], [false, true, false, false, true, true, false, true, false]⟩⟩ 9 ≠ [false] := by decide
  exact bad h.output
end PASoundness.M236.Emit
