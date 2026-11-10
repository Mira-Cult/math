import PASoundness.M236SelectorRoot

/-! A prepared finite tape with a filled gap, anchor, and nine zero-valued
registers. This fixture does not assert blank-start reachability. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Selector.Fixtures
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift

example : entryState 0 = 58 ∧ entryState 8 = 46 := by decide
example : entryState 8 ≠ 58 := by decide

example : rawSystem.Block
    ⟨46, 0, ⟨[true, false, true, true] ++ List.replicate 7 false,
      [true, false, true, true, true, false, true, false, true, false,
       true, false, true, false, true, false, true, false, true, false,
       true, false, true, false, false]⟩⟩ 83
    ⟨79, -1, ⟨[false, true, true] ++ List.replicate 7 false,
      [false, false, false, false, false, true, false, true, false, true,
       false, true, false, true, false, true, false, true, false, true,
       false, true, false, true, true, false]⟩⟩ [] := by
  constructor <;> decide

example : ¬ rawSystem.Block
    ⟨46, 0, ⟨[true, false, true, true] ++ List.replicate 7 false,
      [true, false, true, true, true, false, true, false, true, false,
       true, false, true, false, true, false, true, false, true, false,
       true, false, true, false, false]⟩⟩ 82
    ⟨79, -1, ⟨[false, true, true] ++ List.replicate 7 false,
      [false, false, false, false, false, true, false, true, false, true,
       false, true, false, true, false, true, false, true, false, true,
       false, true, false, true, true, false]⟩⟩ [] := by
  intro h
  have bad : rawSystem.advance
      ⟨46, 0, ⟨[true, false, true, true] ++ List.replicate 7 false,
        [true, false, true, true, true, false, true, false, true, false,
         true, false, true, false, true, false, true, false, true, false,
         true, false, true, false, false]⟩⟩ 82 ≠
      ⟨79, -1, ⟨[false, true, true] ++ List.replicate 7 false,
        [false, false, false, false, false, true, false, true, false, true,
         false, true, false, true, false, true, false, true, false, true,
         false, true, false, true, true, false]⟩⟩ := by decide
  exact bad h.endpoint

end PASoundness.M236.Selector.Fixtures
