import PASoundness.PAtoCompactUnaryGraphFunctional
import PASoundness.PAtoCompactCancellationGuardInputs

/-! Fixed capture-safe alpha transport between the literal canonical quotient
formula and its allocator-100 equivalents at the four distinct alias names.
This is finite K proof data, not dynamic quotient cancellation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCancellationEquivAlpha100
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactUnaryGraphFunctional PASoundness.PAtoCompactEquivNoShadow
open PASoundness.PAtoCompactCancellationGuardInputs
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def outputEquivalent : Formula := replace 0 41 (replace 1 43 equivalentFormula)

private def canonical_forward : KDerivation (imp equivalentFormula.encode (equivAt 100 0 1).encode) := by
  simpa [equivTemplate, normalizeBottom_encode] using (canonical_equiv_alpha 100 (by omega)).forward

private def canonical_backward : KDerivation (imp (equivAt 100 0 1).encode equivalentFormula.encode) := by
  simpa [equivTemplate, normalizeBottom_encode] using (canonical_equiv_alpha 100 (by omega)).backward

/-- Input alias formula and allocator-100 formula represent the same literal
quotient relation in both finite K proof directions. -/
def input_alpha :
    KDerivation (imp inputEquivalent.encode (equivAt 100 40 42).encode) ×
    KDerivation (imp (equivAt 100 40 42).encode inputEquivalent.encode) := by
  let A := equivalentFormula
  let B := equivAt 100 0 1
  have h01 : 0 ≠ 40 := by decide
  have h12 : 1 ≠ 42 := by decide
  have hA0 : 0 ∉ (Formula.imp A B).binders := by decide
  have hA40 : 40 ∉ (Formula.imp A B).binders := by decide
  have hA1 : 1 ∉ (replace 0 40 (Formula.imp A B)).binders := by decide
  have hA42 : 42 ∉ (replace 0 40 (Formula.imp A B)).binders := by decide
  have h0 := universalInstance 0 40 (Formula.imp A B) h01 hA0 hA40
  have h1 := universalInstance 1 42 (replace 0 40 (Formula.imp A B)) h12 hA1 hA42
  have hshape : replace 1 42 (replace 0 40 B) = equivAt 100 40 42 := by decide
  have hfor0 : KDerivation (replace 0 40 (Formula.imp A B)).encode := .mp (.generalize 0 canonical_forward) h0
  have hfor : KDerivation (replace 1 42 (replace 0 40 (Formula.imp A B))).encode := .mp (.generalize 1 hfor0) h1
  have hrB0 : 0 ∉ (Formula.imp B A).binders := by decide
  have hrB40 : 40 ∉ (Formula.imp B A).binders := by decide
  have hrB1 : 1 ∉ (replace 0 40 (Formula.imp B A)).binders := by decide
  have hrB42 : 42 ∉ (replace 0 40 (Formula.imp B A)).binders := by decide
  have hr0 := universalInstance 0 40 (Formula.imp B A) h01 hrB0 hrB40
  have hr1 := universalInstance 1 42 (replace 0 40 (Formula.imp B A)) h12 hrB1 hrB42
  have hback0 : KDerivation (replace 0 40 (Formula.imp B A)).encode := .mp (.generalize 0 canonical_backward) hr0
  have hback : KDerivation (replace 1 42 (replace 0 40 (Formula.imp B A))).encode := .mp (.generalize 1 hback0) hr1
  constructor
  · simpa only [replace, Formula.encode, inputEquivalent, A, B, hshape] using hfor
  · simpa only [replace, Formula.encode, inputEquivalent, A, B, hshape] using hback

/-- Output alias formula and allocator-100 formula agree in both directions. -/
def output_alpha :
    KDerivation (imp outputEquivalent.encode (equivAt 100 41 43).encode) ×
    KDerivation (imp (equivAt 100 41 43).encode outputEquivalent.encode) := by
  let A := equivalentFormula
  let B := equivAt 100 0 1
  have h01 : 0 ≠ 41 := by decide
  have h12 : 1 ≠ 43 := by decide
  have hA0 : 0 ∉ (Formula.imp A B).binders := by decide
  have hA41 : 41 ∉ (Formula.imp A B).binders := by decide
  have hA1 : 1 ∉ (replace 0 41 (Formula.imp A B)).binders := by decide
  have hA43 : 43 ∉ (replace 0 41 (Formula.imp A B)).binders := by decide
  have h0 := universalInstance 0 41 (Formula.imp A B) h01 hA0 hA41
  have h1 := universalInstance 1 43 (replace 0 41 (Formula.imp A B)) h12 hA1 hA43
  have hshape : replace 1 43 (replace 0 41 B) = equivAt 100 41 43 := by decide
  have hsrc : replace 1 43 (replace 0 41 A) = outputEquivalent := by decide
  have hfor0 : KDerivation (replace 0 41 (Formula.imp A B)).encode := .mp (.generalize 0 canonical_forward) h0
  have hfor : KDerivation (replace 1 43 (replace 0 41 (Formula.imp A B))).encode := .mp (.generalize 1 hfor0) h1
  have hrB0 : 0 ∉ (Formula.imp B A).binders := by decide
  have hrB41 : 41 ∉ (Formula.imp B A).binders := by decide
  have hrB1 : 1 ∉ (replace 0 41 (Formula.imp B A)).binders := by decide
  have hrB43 : 43 ∉ (replace 0 41 (Formula.imp B A)).binders := by decide
  have hr0 := universalInstance 0 41 (Formula.imp B A) h01 hrB0 hrB41
  have hr1 := universalInstance 1 43 (replace 0 41 (Formula.imp B A)) h12 hrB1 hrB43
  have hback0 : KDerivation (replace 0 41 (Formula.imp B A)).encode := .mp (.generalize 0 canonical_backward) hr0
  have hback : KDerivation (replace 1 43 (replace 0 41 (Formula.imp B A))).encode := .mp (.generalize 1 hback0) hr1
  constructor
  · simpa only [replace, Formula.encode, hsrc, hshape] using hfor
  · simpa only [replace, Formula.encode, hsrc, hshape] using hback

#print axioms PASoundness.PAtoCompactCancellationEquivAlpha100.input_alpha
#print axioms PASoundness.PAtoCompactCancellationEquivAlpha100.output_alpha
end PASoundness.PAtoCompactCancellationEquivAlpha100
