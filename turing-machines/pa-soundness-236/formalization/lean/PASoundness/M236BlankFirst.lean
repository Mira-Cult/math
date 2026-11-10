import PASoundness.M236UnifiedDecrement
import PASoundness.M236RuntimeGeometry
/-! Extend the certified literal blank-start run through its first named
zero decrement. This is finite execution, not an omega-acceptance proof. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.BlankFirst
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

def zeros : RegisterMachine.Bank 9 := fun _ => 0
def reserve : List Nat := List.replicate 1900 0
def word : List Bool := [false, false, false, false]
def r : Fin 9 := 1

def root : Configuration 237 := ⟨79, -3818,
  ⟨false :: true :: true :: (List.replicate 6 false ++ false :: []),
    word ++ false :: false :: (List.replicate 3815 false ++ true :: false ::
      Redispatch.selectedPayload zeros r reserve [])⟩⟩

theorem path : Preparation.NamedPath Grammar.nodes 157 word
    (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) false .right none) := by
  apply Preparation.NamedPath.step 157 141 false _ _ (by decide)
  apply Preparation.NamedPath.step 141 31 false _ _ (by decide)
  apply Preparation.NamedPath.step 31 2 false _ _ (by decide)
  exact Preparation.NamedPath.leaf 2 false _ (by decide) ⟨_, _, _, _, _, rfl⟩

/-- The prepared root tape differs from the certified tape only by one
explicit trailing blank, which has the same two-way interpretation. -/
theorem root_right : root.tape.right = RuntimeGeometry.entryTape.right ++ [false] := by
  decide

/-- Appending one explicit blank leaves every default-blank read unchanged. -/
theorem getD_append_false (xs : List Bool) (i : Nat) :
    (xs ++ [false]).getD i false = xs.getD i false := by
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

/-- The entire physical raw tape at the certified entry has this root form. -/
theorem root_related : Related root ((machineWordSystem raw rawLabels).run 89821408) := by
  have h := RuntimeCertificate.raw_entry.1
  change Related ⟨79, -3818, (PackedTape.unpackConfig RuntimeCertificate.Part66.state3).tape⟩ _ at h
  rw [RuntimeGeometry.entry_tape_checked] at h
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · intro i
    rw [root_right, getD_append_false]
    exact h.2.2.1 i
  · intro i
    exact h.2.2.2 i

/-- The blank-start selected table reaches a zero decrement and returns to
the grammar root after positive finite additional time, without any event.
This is a single finite segment and does not establish unbounded progress. -/
theorem first_zero_from_blank :
    ∃ (time : Nat) (endHead : Int) (scratch1 scratch2 : Nat) (pcTail : List Bool),
      0 < time ∧
      Related ⟨78, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ []),
          pcTail ++ (List.replicate (3815 + (scratch2 + scratch1 + 3)) false ++ true :: false ::
            (bank (UnaryNine.values zeros ++ reserve) ++ false :: []))⟩⟩
        ((machineWordSystem machine machineLabels).run (89821408 + time)) ∧
      (machineWordSystem machine machineLabels).prefixWord (89821408 + time) = [] ∧
      UnaryCodec.decodeBank (9 + reserve.length) (bank (UnaryNine.values zeros ++ reserve) ++ [false]) =
        some (UnaryNine.values zeros ++ reserve, [false]) ∧
      RegisterMachine.execute (.decNZ r) zeros = ⟨zeros, false, []⟩ := by
  obtain ⟨time, endHead, scratch1, scratch2, pcTail, finish, ht, hp, hr, hq, hd, hout⟩ :=
    DecrementRoot.physical_root_zero zeros r (by rfl) reserve 3815 word false path (-3818) [] []
      ((machineWordSystem raw rawLabels).run 89821408) root_related
  have hstart : mapConfig ((machineWordSystem raw rawLabels).run 89821408) =
      (machineWordSystem machine machineLabels).run 89821408 := by
    rw [machineWordSystem_run, map_run, ← machineWordSystem_run machine machineLabels]
  have hend : (machineWordSystem machine machineLabels).run (89821408 + time) = mapConfig finish := by
    rw [WordEventSystem.run_add, ← hstart]
    exact hq.endpoint
  have houtput : (machineWordSystem machine machineLabels).prefixWord (89821408 + time) = [] := by
    rw [WordEventSystem.prefix_add, RuntimeGeometry.selected_entry_geometry.2, ← hstart, hq.output]
    rfl
  have hrel := FastBootstrap.Certificate.related_map hr
  have hqstate : mapState 79 = 78 := by decide
  change Related ⟨mapState 79, endHead, _⟩ _ at hrel
  rw [hqstate] at hrel
  refine ⟨time, endHead, scratch1, scratch2, pcTail, ht, ?_, houtput, ?_, hout⟩
  · rw [hend]; exact hrel
  · simpa using hd
end PASoundness.M236.BlankFirst
