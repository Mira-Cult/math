import PASoundness.PAtoCompactProductOutputInstantiate
import PASoundness.PAtoCompactProductMatchAliasSafe

/-! Stage the four active product-output labels through the already checked
six-label placeholder schedule. Dummy slots are harmless; arbitrary final
factor and output labels may coincide. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputAliasSafe

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactEquivStepsSyntax PASoundness.PAtoCompactProductMatchAliasSafe
open PASoundness.PAtoCompactProductOutputFixedBase PASoundness.PAtoCompactProductOutputInstantiate

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Apply an explicit sequence of safe name replacements to the output frame. -/
def instantiate_steps (b : Nat) : (steps : List (Nat × Nat)) →
    (∀ p ∈ steps, p.1 < b ∧ p.2 < b + 2) →
    (x y p q : Nat) → KDerivation (PAtoCompactProductOutputFixedBase.frame b x y p q).encode →
      KDerivation (PAtoCompactProductOutputFixedBase.frame b (applySteps steps x) (applySteps steps y)
        (applySteps steps p) (applySteps steps q)).encode
  | [], _, _, _, _, _, h => h
  | (r,s) :: rest, safe, x, y, p, q, h => by
    have hrs := safe (r,s) (by simp)
    have htail : ∀ t ∈ rest, t.1 < b ∧ t.2 < b + 2 := by
      intro t ht
      exact safe t (by simp [ht])
    have hnext := PAtoCompactProductOutputInstantiate.instantiate_name b x y p q r s hrs.1 hrs.2 h
    exact instantiate_steps b rest htail (rename r s x) (rename r s y) (rename r s p) (rename r s q) hnext

/-- All four endpoint labels may alias. The chosen base is above all of them. -/
noncomputable def alias_safe_output (x y p q : Nat) :
    KDerivation (PAtoCompactProductOutputFixedBase.frame (chosenBase p 0 0 q x y) x y p q).encode := by
  let b := chosenBase p 0 0 q x y
  have hb : 44 < b + 2 := by dsimp [b, chosenBase, placeholder]; omega
  have h0 : KDerivation (PAtoCompactProductOutputFixedBase.frame b 43 44 0 42).encode :=
    fixed_base_output b hb
  have h := instantiate_steps b (stages p 0 0 q x y) (stages_safe p 0 0 q x y) 43 44 0 42 h0
  rcases stages_values p 0 0 q x y with ⟨h0',h1',h2',h42',h43',h44'⟩
  simpa [b, h0', h42', h43', h44'] using h

theorem alias_safe_output_certificate (x y p q : Nat) :
    theoremCode (certificate (alias_safe_output x y p q)) =
      (PAtoCompactProductOutputFixedBase.frame (chosenBase p 0 0 q x y) x y p q).encode := certificate_correct _

end PASoundness.PAtoCompactProductOutputAliasSafe

#print axioms PASoundness.PAtoCompactProductOutputAliasSafe.instantiate_steps
#print axioms PASoundness.PAtoCompactProductOutputAliasSafe.alias_safe_output
#print axioms PASoundness.PAtoCompactProductOutputAliasSafe.alias_safe_output_certificate
