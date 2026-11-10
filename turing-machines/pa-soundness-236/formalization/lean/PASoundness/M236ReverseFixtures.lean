import PASoundness.M236Reverse

/-! Checks for the bound/free name convention and guarded numeric codes. -/
namespace PASoundness.M236ReverseFixtures

open PASoundness.CompactMatrix PASoundness.M236Reverse

example : varName 3 0 = 4 := rfl
example : varName 3 2 = 0 := rfl
example : varName 3 3 = 1 := rfl
example : varName 3 4 = 3 := rfl
example : varName 123 456 = 667 := rfl

example (f : Formula) : PASoundness.RawMatrix.encodeFormula (padded f) ≠ 1 := by
  have h := padded_code_ge_four f
  omega

example (f : Formula) : PASoundness.RawMatrix.encodeFormula (padded f) ≠ 3 := by
  have h := padded_code_ge_four f
  omega

end PASoundness.M236ReverseFixtures
