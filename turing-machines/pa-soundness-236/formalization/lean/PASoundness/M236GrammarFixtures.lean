import PASoundness.M236GrammarIntegration

/-! Kernel-checked examples of actual grammar paths, including both fused
output polarities. These finite prepared tapes do not establish reachability
from the blank start. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Grammar.Fixtures
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift

example : LeafPath nodes 157 [false, true, false, false, true, true, true, false] := by
  apply LeafPath.step 157 141 false _ (by decide)
  apply LeafPath.step 141 140 true _ (by decide)
  apply LeafPath.step 140 82 false _ (by decide)
  apply LeafPath.step 82 36 false _ (by decide)
  apply LeafPath.step 36 25 true _ (by decide)
  apply LeafPath.step 25 19 true _ (by decide)
  apply LeafPath.step 19 18 true _ (by decide)
  exact LeafPath.leaf 18 false "emit.0" 72 true .left (some false) (by decide)

example : LeafPath nodes 157 [false, true, false, false, true, true, false, true, false] := by
  apply LeafPath.step 157 141 false _ (by decide)
  apply LeafPath.step 141 140 true _ (by decide)
  apply LeafPath.step 140 82 false _ (by decide)
  apply LeafPath.step 82 36 false _ (by decide)
  apply LeafPath.step 36 25 true _ (by decide)
  apply LeafPath.step 25 19 true _ (by decide)
  apply LeafPath.step 19 16 false _ (by decide)
  apply LeafPath.step 16 15 true _ (by decide)
  exact LeafPath.leaf 15 false "emit.1" 72 true .left (some true) (by decide)

example : rawSystem.wordFrom
    ⟨79, 0, ⟨[], [false, true, false, false, true, true, true, false]⟩⟩ 8 = [false] := by decide
example : rawSystem.wordFrom
    ⟨79, 0, ⟨[], [false, true, false, false, true, true, false, true, false]⟩⟩ 9 = [true] := by decide
example : rawSystem.wordFrom
    ⟨79, 0, ⟨[], [false, true, false, false, true, true, true, false]⟩⟩ 8 ≠ [true] := by decide

end PASoundness.M236.Grammar.Fixtures
