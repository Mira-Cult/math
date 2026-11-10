import PASoundness.M236Named

/-! Binder shadowing, disjoint free slots, and the two independent parameters
of the named-to-positional challenge translation. -/
namespace PASoundness.M236NamedFixtures

open PASoundness.CompactMatrix PASoundness.M236Named PASoundness.M236Positional
open PASoundness.M236Definitions

example : index (challengeSlot 2) [2, 2] 2 = 0 := rfl
example : index (challengeSlot 2) [2, 2] 7 = 12 := rfl
example : index (challengeSlot 2) [3, 2] 2 = 1 := rfl

example (ρ : Environment) :
    ∃ e, PASoundness.M236Game.lookup e 0 = 123 ∧
      PASoundness.M236Game.lookup e 1 = 456 ∧ ∀ y,
        (Truth4 (toFour (.all 2 (.equal 2 7)) [] (challengeSlot 2))
          (y :: unpackEnv e) ↔
          (Formula.all 2 (.equal 2 7)).Realize (update ρ 2 y)) :=
  named_predicate_positional _ ρ 2 123 456

end PASoundness.M236NamedFixtures
