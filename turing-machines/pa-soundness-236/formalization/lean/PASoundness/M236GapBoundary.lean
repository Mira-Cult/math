import PASoundness.M236AdjacentCoverage
import PASoundness.M236Emit
/-! A literal local counterexample to dropping the normal-return gap bound. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.GapBoundary
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

def word : List Bool := [true, true, false, false]
def next : List Bool := [true, true, false, true, false, false, false, false, false]
def returned : List Bool := [true, true, false, true]
def r : Fin 9 := 3

theorem path : Preparation.NamedPath Grammar.nodes 157 word
    (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) false .right none) := by
  apply Preparation.NamedPath.step 157 156 true _ _ (by decide)
  apply Preparation.NamedPath.step 156 155 true _ _ (by decide)
  apply Preparation.NamedPath.step 155 144 false _ _ (by decide)
  exact Preparation.NamedPath.leaf 144 false _ (by decide) ⟨_, _, _, _, _, rfl⟩

theorem adjacent : (word, next) ∈ Control.adjacentPaths := by decide

theorem expected_path : Preparation.NamedPath Grammar.nodes 157 next
    (.leaf "3.k.rest.decnz" 51 false .right none) := by
  apply Preparation.NamedPath.step 157 156 true _ _ (by decide)
  apply Preparation.NamedPath.step 156 155 true _ _ (by decide)
  apply Preparation.NamedPath.step 155 144 false _ _ (by decide)
  apply Preparation.NamedPath.step 144 143 true _ _ (by decide)
  apply Preparation.NamedPath.step 143 142 false _ _ (by decide)
  apply Preparation.NamedPath.step 142 25 false _ _ (by decide)
  apply Preparation.NamedPath.step 25 14 false _ _ (by decide)
  apply Preparation.NamedPath.step 14 11 false _ _ (by decide)
  exact Preparation.NamedPath.leaf 11 false _ (by decide) ⟨_, _, _, _, _, rfl⟩

theorem decoded : Control.decodeOne word = some (false, returned) := by decide

theorem requires_five : next.length - returned.length = 5 := by decide

/-- With only two zeros before the anchor, the actual input cannot be the
adjacent path; this is independent of the arbitrary trailing tape. -/
theorem wrong_prefix (tail : List Bool) :
    (returned ++ false :: false :: true :: false :: tail).take next.length ≠ next := by
  simp [returned, next, List.take]

/-- At the stated prepared tape, this actual positive-decrement segment returns
with exactly two zeros before its anchor and no event. No blank reachability is
asserted. -/
theorem physical_zero_gap (registers : RegisterMachine.Bank 9) (value : Nat)
    (hvalue : registers r = value + 1) (reserve : List Nat)
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate 0 false ++ true :: false ::
          Redispatch.selectedPayload registers r reserve tail)⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (finish : Config 237), 0 < time ∧
      (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          returned ++ false :: false :: true :: false ::
            (bank (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0])) ++ tail)⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] ∧
      (returned ++ false :: false :: true :: false ::
        (bank (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0])) ++ tail)).take next.length ≠ next := by
  obtain ⟨runs, rest, time, endHead, scratch, bit, pcTail, finish,
    hword, hsplit, hprefix, ht, hp, hr, hq, hd, hout⟩ :=
    DecrementRoot.physical_root_positive_detail registers r value hvalue reserve 0 word false path head left tail c hrel
  have hzero : scratch = 0 := by
    cases scratch with
    | zero => rfl
    | succ n =>
      rw [hword] at hsplit
      simp [word, List.replicate_succ] at hsplit
  have hdec := Control.decodeOne_of_split runs rest word scratch bit pcTail hword hsplit hprefix
  rw [decoded] at hdec
  cases hdec
  subst scratch
  refine ⟨time, endHead, finish, ht, hp, ?_, hq, wrong_prefix _⟩
  simpa using hr
def initialBank : RegisterMachine.Bank 9 := fun q => if q = r then 1 else 0
def divertedWord : List Bool := [true, true, false, true, false, false, true, false, true, false]

theorem diverted_path : Preparation.NamedPath Grammar.nodes 157 divertedWord
    (.leaf (Emit.emitName true) 72 true .left (some true)) := by
  apply Preparation.NamedPath.step 157 156 true _ _ (by decide)
  apply Preparation.NamedPath.step 156 155 true _ _ (by decide)
  apply Preparation.NamedPath.step 155 144 false _ _ (by decide)
  apply Preparation.NamedPath.step 144 143 true _ _ (by decide)
  apply Preparation.NamedPath.step 143 142 false _ _ (by decide)
  apply Preparation.NamedPath.step 142 25 false _ _ (by decide)
  apply Preparation.NamedPath.step 25 19 true _ _ (by decide)
  apply Preparation.NamedPath.step 19 16 false _ _ (by decide)
  apply Preparation.NamedPath.step 16 15 true _ _ (by decide)
  exact Preparation.NamedPath.leaf 15 false _ (by decide) ⟨_, _, _, _, _, rfl⟩

theorem bank_after :
    UnaryNine.values (RegisterMachine.execute (.decNZ r) initialBank).bank = List.replicate 9 0 := by decide

theorem diverted_tape :
    returned ++ false :: false :: true :: false ::
      bank (List.replicate 9 0 ++ [0]) = divertedWord ++ bank (List.replicate 9 0) := by decide

def initialZipper : Configuration 237 :=
  ⟨79, 0, ⟨false :: true :: true :: List.replicate 7 false,
    word ++ false :: false :: true :: false :: Redispatch.selectedPayload initialBank r [] []⟩⟩

def initialConfig : Config 237 := Redispatch.realizeConfig initialZipper

/-- On this explicitly prepared zero-gap full tape, the literal raw machine
performs the decrement and then emits true rather than following the adjacent
path. The quotient has exactly the same event. This is not a blank-run claim. -/
theorem concrete_unexpected_event :
    ∃ (time : Nat) (endHead : Int) (mid finish : Config 237), 0 < time ∧
      (machineWordSystem raw rawLabels).Block initialConfig time mid [] ∧
      (machineWordSystem raw rawLabels).Block initialConfig (time + divertedWord.length) finish [true] ∧
      (machineWordSystem machine machineLabels).Block (mapConfig initialConfig)
        (time + divertedWord.length) (mapConfig finish) [true] ∧
      (returned ++ false :: false :: true :: false :: bank (List.replicate 9 0 ++ [0])).take next.length ≠ next := by
  have hin : Related ⟨79, 0,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: []),
        word ++ false :: false :: (List.replicate 0 false ++ true :: false ::
          Redispatch.selectedPayload initialBank r [] [])⟩⟩ initialConfig := by
    simpa [initialConfig, initialZipper, List.replicate_succ] using Redispatch.realize_related initialZipper
  obtain ⟨time, endHead, mid, ht, hp, hr, hq, bad⟩ := physical_zero_gap initialBank 0 (by decide) [] 0 [] [] initialConfig hin
  have hr' : Related ⟨79, endHead,
      ⟨false :: true :: true :: (List.replicate 7 false ++ []), divertedWord ++ bank (List.replicate 9 0)⟩⟩ mid := by
    rw [bank_after] at hr
    simp only [List.nil_append, List.append_nil] at hr
    rw [diverted_tape] at hr
    exact hr
  obtain ⟨pre, last, finish, hw, hp', hr'', hq', ht'⟩ := Emit.physical_named_emit true divertedWord 72 true .left
    diverted_path endHead (false :: true :: true :: (List.replicate 7 false ++ []))
    (bank (List.replicate 9 0)) mid hr'
  exact ⟨time, endHead, mid, finish, ht, hp,
    by simpa using hp.trans (machineWordSystem raw rawLabels) hp',
    by simpa using hq.trans (machineWordSystem machine machineLabels) hq', wrong_prefix _⟩
end PASoundness.M236.GapBoundary
