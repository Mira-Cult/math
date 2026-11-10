import PASoundness.M236Definitions

/-! Parameter and sentinel controls; no finite example proves the endpoint. -/
namespace PASoundness.M236DefinitionsFixtures

open PASoundness.M236Game PASoundness.M236Definitions

theorem definitions_distinguish (n m : Nat) (h : m ≠ n) :
    ¬ Truth (numeral n 0) [m] := by
  intro ht
  have he := (numeral_truth n 0 [m]).mp ht
  exact h (by simpa using he)

theorem two_parameters (f y a b : Nat) :
    Truth (specialize f [a, b]) [y] ↔ Truth f [y, a, b] :=
  specialize_truth f [a, b] y

theorem collapsed_zero_tail : packEnv [0, 0] = 0 ∧ unpackEnv 0 = [] := by
  constructor
  · simp [packEnv, PASoundness.Cantor.pair, PASoundness.Cantor.triangle]
  · simp [unpackEnv]

/-- Despite the zero-pair collapse, every finite coordinate is preserved. -/
theorem collapsed_tail_agrees (i : Nat) :
    (unpackEnv (packEnv [0, 0])).getD i 0 = ([0, 0] : List Nat).getD i 0 :=
  unpack_pack_agrees [0, 0] i

end PASoundness.M236DefinitionsFixtures
