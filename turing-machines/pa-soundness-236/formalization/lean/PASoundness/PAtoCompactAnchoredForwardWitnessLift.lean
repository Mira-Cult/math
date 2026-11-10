import PASoundness.PAtoCompactAnchoredForwardSharedProjection
import PASoundness.PAtoCompactScopedRowLexLift
import PASoundness.PAtoCompactFreeVacuity

/-! A K proof-data lift from the actual nested anchored-product witness
package to the forward shared context, retaining all four original witnesses
and the cut, old-graph and clean-map conjuncts. The candidate/successor guards
are explicit. This does not establish a product matrix, multiplication
totality, or PA soundness. -/
namespace PASoundness.PAtoCompactAnchoredForwardWitnessLift
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactAnchoredProductWitnessPackage PASoundness.PAtoCompactCleanSuffixRowPackage
open PASoundness.PAtoCompactProductCleanRowJoint PASoundness.PAtoCompactCleanSuffixRow64
open PASoundness.PAtoCompactAnchoredLexSharedProjection PASoundness.PAtoCompactAnchoredForwardSharedProjection
open PASoundness.PAtoCompactFixedFirstRowGraph64 PASoundness.PAtoCompactScopedRowLexLift
set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The external candidate and successor guards, with their displayed free
labels. None of the four witness labels occurs free here. -/
def guards : Formula := namedBoth (domainAt 100 30)
  (namedBoth (domainAt 100 32) (namedBoth (domainAt 100 45) (namedSuccessor 30 38 39)))

/-- Strong retained form: under the same suffix, old graph, clean map and row
graph, keep the original conjuncts while adding the forward context. -/
def retainedResult : Nat := nested suffixData.encode oldBody.encode cleanMatrix.encode
  PASoundness.PAtoCompactMultiplicationForwardSharedContext.context.encode

private def GAB : Formula := namedBoth (namedBoth guards suffixData) oldBody
private def GABC : Formula := namedBoth GAB cleanMatrix

private def point : KDerivation (imp GABC.encode (imp rowBody64.encode
    PASoundness.PAtoCompactMultiplicationForwardSharedContext.context.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [rowBody64.encode,GABC.encode]
  have hr : Context Γ rowBody64.encode := .head _ _
  have hh : Context Γ GABC.encode := .hypothesis (by simp [Γ])
  have hh' : Context Γ (both (both (both guards.encode suffixData.encode) oldBody.encode)
      cleanMatrix.encode) := by
    simpa [GABC,GAB,namedBoth,Formula.not,Formula.encode,both,neg] using hh
  have hc := Context.conjunctionRight hh'
  have hob := Context.conjunctionLeft hh'
  have ho := Context.conjunctionRight hob
  have hga := Context.conjunctionLeft hob
  have ha := Context.conjunctionRight hga
  have hg := Context.conjunctionLeft hga
  have hg' : Context Γ (both (domainAt 100 30).encode
      (both (domainAt 100 32).encode (both (domainAt 100 45).encode
        (successorCode 30 38 39)))) := by
    simpa [guards,namedBoth,namedSuccessor,namedSuccessorBody,namedEither,
      Formula.not,Formula.encode,successorCode,both,neg,either] using hg
  have h30 := Context.conjunctionLeft hg'
  have h32 := Context.conjunctionLeft (Context.conjunctionRight hg')
  have h45 := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hg'))
  have hs := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg'))
  exact .mp hs (.mp hr (.mp hc (.mp ho (.mp ha (.mp h45 (.mp h32
    (.mp h30 (.closed forward_from_components))))))))

/-- Preserve the same suffix 40, old graph 10, map graph 6, and row graph 64
while adjoining the derived forward context. -/
def retain_forward : KDerivation (imp guards.encode (imp anchoredResult.encode retainedResult)) := by
  have v40 := free_vacuity 40 guards (by decide)
  have v10 := free_vacuity 10 (namedBoth guards suffixData) (by decide)
  have v6 := free_vacuity 6 GAB (by decide)
  have v64 := free_vacuity 64 GABC (by decide)
  have h := lift_scoped guards.encode suffixData.encode oldBody.encode cleanMatrix.encode
    rowBody64.encode PASoundness.PAtoCompactMultiplicationForwardSharedContext.context.encode
    v40 (by simpa [namedBoth,Formula.not,Formula.encode,both,neg] using v10)
    (by simpa [GAB,namedBoth,Formula.not,Formula.encode,both,neg] using v6)
    (by simpa [GABC,GAB,namedBoth,Formula.not,Formula.encode,both,neg] using v64)
    (by simpa [GABC,GAB,namedBoth,Formula.not,Formula.encode,both,neg] using point)
  simpa [retainedResult,nested,anchoredResult,jointResult,result64,oldBody,
    namedBoth,Formula.not,Formula.encode,both,neg] using h

theorem retain_forward_certificate : theoremCode (certificate retain_forward) =
    imp guards.encode (imp anchoredResult.encode retainedResult) := certificate_correct _
end PASoundness.PAtoCompactAnchoredForwardWitnessLift
#print axioms PASoundness.PAtoCompactAnchoredForwardWitnessLift.retain_forward
#print axioms PASoundness.PAtoCompactAnchoredForwardWitnessLift.retain_forward_certificate
