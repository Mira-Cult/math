import PASoundness.M236Weakening

/-! Binder-sensitive controls for the strict-atom translations. -/
namespace PASoundness.M236WeakeningFixtures

open PASoundness.M236Game PASoundness.M236Weakening

/-- Insertion behind an existing binder preserves its head and shifts all
outer parameters, including positions beyond the finite list's end. -/
theorem insert_below_binder (f x inserted : Nat) (env : List Nat) :
    Truth (weaken f 1) (x :: inserted :: env) ↔ Truth f (x :: env) :=
  weaken_truth f 1 _ _ (compatible_cons (compatible_front inserted env) x)

/-- Unrestricted atoms with self, forward and reversed indices all have
strict-language translations with the exact same meaning. -/
theorem unrestricted_atoms (env : List Nat) :
    (Truth (memberCode 0 0) env ↔ (env.getD 0 0).testBit (env.getD 0 0) = true) ∧
    (Truth (memberCode 0 3) env ↔ (env.getD 0 0).testBit (env.getD 3 0) = true) ∧
    (Truth (memberCode 3 0) env ↔ (env.getD 3 0).testBit (env.getD 0 0) = true) :=
  ⟨member_truth 0 0 env, member_truth 0 3 env, member_truth 3 0 env⟩

/-- The old numeric code zero denotes self-membership, unlike strict code
zero, and its translation retains that meaning. -/
theorem old_zero_translation (env : List Nat) :
    Truth (toStrict (parityToCantor 0)) env ↔
      (env.getD 0 0).testBit (env.getD 0 0) = true := by
  rw [toStrict_truth, parityToCantor_truth]
  rw [parityTruth]
  simp [PASoundness.Cantor.unpair, PASoundness.Cantor.unpairAux]

end PASoundness.M236WeakeningFixtures
