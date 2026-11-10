import PASoundness.PAtoCompactEquivalentEndpointAlias
import PASoundness.CompactQuantifiers

/-! Capture-safe finite K elimination of the predecessor endpoint guards in
the fixed-name successor-cancellation proof. This yields the canonical
isomorphism syntax instantiated at fresh names 40 and 42; it does not by
itself lift cancellation to arbitrary dynamic allocators or eliminate the
quotient-successor witness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCancellationGuardInputs
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactRestrictedEquivalentTarget
open PASoundness.PAtoCompactEquivalentAliasInstantiation PASoundness.PAtoCompactEquivalentAliasGuardLift
open PASoundness.PAtoCompactEquivalentEndpointAlias
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The canonical quotient formula with predecessor values at names 40,42. -/
def inputEquivalent : Formula := replace 1 42 (replace 0 40 equivalentFormula)

/-- Both endpoint equality guards eliminate the existential alias conclusion;
the output is the original quotient formula at noncapturing names 40,42. -/
def guard_to_input_equiv : KDerivation (imp (equal 40 2) (imp (equal 42 5)
    (imp (guarded originalAliases).encode inputEquivalent.encode))) := by
  let f : Formula := .imp preparedEquivalent equivalentFormula
  have d : KDerivation f.encode := prepare_equivalent.backward
  have i0 := universalInstance 0 40 f (by decide) (by decide) (by decide)
  have d0 : KDerivation (replace 0 40 f).encode := .mp (.generalize 0 d) i0
  have i1 := universalInstance 1 42 (replace 0 40 f) (by decide) (by decide) (by decide)
  have d1 : KDerivation (replace 1 42 (replace 0 40 f)).encode := .mp (.generalize 1 d0) i1
  have he1 := (equalityReplace 2 40 endpointTarget (by decide) (by decide)).1
  let f1 := replace 2 40 endpointTarget
  have he2 := (equalityReplace 5 42 f1 (by decide) (by decide)).1
  have hs : replace 5 42 f1 = replace 1 42 (replace 0 40 preparedEquivalent) := by decide
  rw [hs] at he2
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(guarded originalAliases).encode,equal 42 5,equal 40 2]
  have hg : Context Γ (guarded originalAliases).encode := Context.head _ _
  have h40 : Context Γ (equal 40 2) := .hypothesis (by simp [Γ])
  have h42 : Context Γ (equal 42 5) := .hypothesis (by simp [Γ])
  have hp : Context Γ endpointTarget.encode := .mp hg (.closed PASoundness.PAtoCompactEquivalentEndpointAlias.forward)
  have hp' : Context Γ f1.encode := .mp hp (.mp (Context.eqSymm h40) (.closed he1))
  have hp'' : Context Γ (replace 1 42 (replace 0 40 preparedEquivalent)).encode :=
    .mp hp' (.mp (Context.eqSymm h42) (.closed he2))
  exact .mp hp'' (.closed d1)

theorem guard_to_input_equiv_certificate : theoremCode (certificate guard_to_input_equiv) =
    imp (equal 40 2) (imp (equal 42 5) (imp (guarded originalAliases).encode inputEquivalent.encode)) :=
  certificate_correct _

end PASoundness.PAtoCompactCancellationGuardInputs

#print axioms PASoundness.PAtoCompactCancellationGuardInputs.guard_to_input_equiv
#print axioms PASoundness.PAtoCompactCancellationGuardInputs.guard_to_input_equiv_certificate
