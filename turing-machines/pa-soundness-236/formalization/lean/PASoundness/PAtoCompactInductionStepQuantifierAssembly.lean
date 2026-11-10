import PASoundness.PAtoCompactQuantifiedRefutation

/-! Quantification of a candidate-restricted pointwise induction step.
The caller supplies the actual pointwise K derivation and explicit K vacuity
proofs for the retained assumptions. This is not a PA induction translation:
it does not construct the pointwise substitution alignment, parameter guards,
or the vacuity proofs. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactInductionStepQuantifierAssembly

open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactUniformStep PASoundness.PAtoCompactQuantifiedRefutation
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The three generalizations retain `G`, `A`, and the candidate condition
under the first two binders and only `G` and `A` under the container binder.
All supplied vacuity arguments are finite K derivations; no side-condition
about free names is silently inferred. -/
def quantified_restricted_step
    (G A C Y t y m w p q : Nat) (f : CompactNamed.Formula)
    (pointwise : KDerivation (imp G (imp A (imp C
      (imp (predecessorCore Y y m w p q)
        (imp (CompactNamed.replace t y f).encode (CompactNamed.replace t m f).encode))))))
    (vacY : ∀ h, h ∈ [A,G] → KDerivation (imp h (allCode Y h)))
    (vacy : ∀ h, h ∈ [C,A,G] → KDerivation (imp h (allCode y h)))
    (vacm : ∀ h, h ∈ [C,A,G] → KDerivation (imp h (allCode m h))) :
    KDerivation (imp G (imp A (allCode Y (imp C (allStepsCode Y t y m w p q f))))) := by
  let Γ := [C,A,G]
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hp : Context Γ (imp (predecessorCore Y y m w p q)
      (imp (CompactNamed.replace t y f).encode (CompactNamed.replace t m f).encode)) :=
    .mp hc (.mp ha (.mp hg (.closed pointwise)))
  have hy : Context Γ (uniformStepCode Y t y m w p q f) :=
    Context.generalize y vacy hp
  have hm : Context Γ (allStepsCode Y t y m w p q f) :=
    Context.generalize m vacm hy
  have hC : Context [A,G] (imp C (allStepsCode Y t y m w p q f)) :=
    Context.deduction hm
  have hY : Context [A,G] (allCode Y (imp C (allStepsCode Y t y m w p q f))) :=
    Context.generalize Y vacY hC
  exact Context.closeEmpty (Context.deduction (Context.deduction hY))

theorem quantified_restricted_step_certificate
    (G A C Y t y m w p q : Nat) (f : CompactNamed.Formula)
    (pointwise : KDerivation (imp G (imp A (imp C
      (imp (predecessorCore Y y m w p q)
        (imp (CompactNamed.replace t y f).encode (CompactNamed.replace t m f).encode))))))
    (vacY : ∀ h, h ∈ [A,G] → KDerivation (imp h (allCode Y h)))
    (vacy : ∀ h, h ∈ [C,A,G] → KDerivation (imp h (allCode y h)))
    (vacm : ∀ h, h ∈ [C,A,G] → KDerivation (imp h (allCode m h))) :
    theoremCode (certificate (quantified_restricted_step G A C Y t y m w p q f
      pointwise vacY vacy vacm)) =
        imp G (imp A (allCode Y (imp C (allStepsCode Y t y m w p q f)))) :=
  certificate_correct _

end PASoundness.PAtoCompactInductionStepQuantifierAssembly

#print axioms PASoundness.PAtoCompactInductionStepQuantifierAssembly.quantified_restricted_step
#print axioms PASoundness.PAtoCompactInductionStepQuantifierAssembly.quantified_restricted_step_certificate
