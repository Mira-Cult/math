import PASoundness.PAtoCompactAdditionRightZeroConverse
import PASoundness.PAtoCompactAdditionIdentityClosedCut

/-! Literal guarded right-zero schema for the proposed addition relation.

This combines two explicit K derivations. The zero graph remains a premise;
no graph totality, functionality, or full PA interpretation is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionRightZeroSchema
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactEmptyExtrema
open PASoundness.PAtoCompactOrdinalAddition
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- For a displayed zero, the literal addition relation and quotient equality
are equivalent for all displayed left and result objects. -/
def right_zero_schema : KDerivation
    (imp (zeroCode 31 36)
      (allCode 30 (allCode 32
        (both (imp additionFormula.encode (equivAt 30 32).encode)
          (imp (equivAt 30 32).encode additionFormula.encode))))) := by
  let Z := zeroCode 31 36
  let A := additionFormula.encode
  let E := (equivAt 30 32).encode
  let Γ := [Z]
  apply Context.closeEmpty
  apply Context.deduction
  have hz : Context Γ Z := Context.head [] _
  have h₁ : Context Γ (imp A E) :=
    .mp hz (.closed PAtoCompactAdditionRightZeroConverse.addition_zero_right_converse)
  have h₂ : Context Γ (imp E A) :=
    .mp hz (.closed PAtoCompactAdditionIdentityClosedCut.addition_of_zero_right)
  have hboth : Context Γ (both (imp A E) (imp E A)) := Context.conjunctionIntro h₁ h₂
  have hv32 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 32 h)) := by
    intro h hh
    have he : h = Z := by simpa [Γ] using hh
    subst h
    exact zero_vacuity 31 36 32 (by decide) (by decide)
  have hv30 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 30 h)) := by
    intro h hh
    have he : h = Z := by simpa [Γ] using hh
    subst h
    exact zero_vacuity 31 36 30 (by decide) (by decide)
  exact Context.generalize 30 hv30 (Context.generalize 32 hv32 hboth)

theorem right_zero_schema_certificate :
    theoremCode (certificate right_zero_schema) =
      imp (zeroCode 31 36)
        (allCode 30 (allCode 32
          (both (imp additionFormula.encode (equivAt 30 32).encode)
            (imp (equivAt 30 32).encode additionFormula.encode)))) :=
  certificate_correct right_zero_schema

end PASoundness.PAtoCompactAdditionRightZeroSchema

#print axioms PASoundness.PAtoCompactAdditionRightZeroSchema.right_zero_schema
#print axioms PASoundness.PAtoCompactAdditionRightZeroSchema.right_zero_schema_certificate
