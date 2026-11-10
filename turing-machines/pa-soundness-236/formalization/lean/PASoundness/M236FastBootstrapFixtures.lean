import PASoundness.M236FastBootstrap

/-! Controls for invalid patterns, wrong states and zero-length shortcuts. -/
namespace PASoundness.M236.FastBootstrap.Fixtures

open PASoundness.M236.FiniteTape

example : scanRight 1 ⟨[], [false]⟩ = none := by decide
example : scanLeft 1 ⟨[true], [true]⟩ = none := by decide
example : scanFill 1 ⟨[true], [true]⟩ = none := by decide
example : perform (.right 0) ⟨77, 0, ⟨[], [true, false]⟩⟩ = none := by decide
example : perform (.right 1) ⟨75, 0, ⟨[], [true, false]⟩⟩ = none := by decide
example : perform (.right 1) ⟨77, 0, ⟨[], [true, false]⟩⟩ =
    some (⟨77, 2, ⟨[false, true], []⟩⟩, 2, []) := by decide

end PASoundness.M236.FastBootstrap.Fixtures
