import PASoundness.M236GapInvariant
import PASoundness.M236BlankSixth
/-! Canonical nine-register bank representation at any selected register. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

theorem selected_payload_bank (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (reserve : List Nat) (tail : List Bool) :
    Redispatch.selectedPayload registers r reserve tail =
      bank (UnaryNine.values registers ++ reserve) ++ false :: tail := by
  rw [UnaryIncrementNine.values_split registers r]
  simp [Redispatch.selectedPayload, UnaryIncrement.bank_append, bank, List.append_assoc, List.replicate_succ]
/-- A default-blank canonical tape can be presented to any selected register
operation, including the physical implementation's explicit trailing zero. -/
theorem related_selected_from_canonical (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (reserve : List Nat) (wirePrefix : List Bool) (head : Int) (left : List Bool) (c : Config 237)
    (h : Related ⟨79, head, ⟨left, wirePrefix ++ bank (UnaryNine.values registers ++ reserve)⟩⟩ c) :
    Related ⟨79, head, ⟨left, wirePrefix ++ Redispatch.selectedPayload registers r reserve []⟩⟩ c := by
  have hh := BlankFirst.related_append_false h
  simpa [selected_payload_bank, List.append_assoc] using hh

/-- An explicit trailing zero can also be removed without changing the full
two-way tape represented by the zipper. -/
theorem related_drop_false {q : Fin 237} {head : Int} {left right : List Bool} {c : Config 237}
    (h : Related ⟨q, head, ⟨left, right ++ [false]⟩⟩ c) :
    Related ⟨q, head, ⟨left, right⟩⟩ c := by
  obtain ⟨hs, hh, hr, hl⟩ := h
  refine ⟨hs, hh, ?_, hl⟩
  intro i
  rw [← BlankFirst.getD_append_false right i]
  exact hr i
/-- The certified raw blank run enters the canonical nine-register tape with
more than the 25 cells required by the literal leaf-depth bound. -/
theorem raw_initial_canonical_budget :
    Related ⟨79, -3818,
      ⟨false :: true :: true :: (List.replicate 7 false ++ []),
        BlankFirst.word ++ false :: false :: (List.replicate 3815 false ++ true :: false ::
          bank (UnaryNine.values BlankFirst.zeros ++ BlankFirst.reserve))⟩⟩
      ((machineWordSystem raw rawLabels).run 89821408) ∧
    25 ≤ 3815 + BlankFirst.word.length ∧
    (machineWordSystem raw rawLabels).prefixWord 89821408 = [] := by
  have hl : List.replicate 6 false ++ false :: [] = List.replicate 7 false ++ [] := by decide
  have h : Related ⟨79, -3818,
      ⟨false :: true :: true :: (List.replicate 7 false ++ []),
        (BlankFirst.word ++ false :: false :: (List.replicate 3815 false ++ true :: false ::
          bank (UnaryNine.values BlankFirst.zeros ++ BlankFirst.reserve))) ++ [false]⟩⟩
      ((machineWordSystem raw rawLabels).run 89821408) := by
    simpa only [BlankFirst.root, selected_payload_bank, hl, List.append_assoc, List.cons_append] using BlankFirst.root_related
  exact ⟨related_drop_false h, by decide, RuntimeCertificate.raw_entry.2⟩
end PASoundness.M236.Control
