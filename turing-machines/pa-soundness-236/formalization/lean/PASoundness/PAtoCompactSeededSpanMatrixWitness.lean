import PASoundness.PAtoCompactSeededSpanMatrixConsolidated
import PASoundness.PAtoCompactSeededSpanInduction

/-! Feed the collector's actual existential graph witness to the conditional
matrix construction. All non-graph hypotheses are literal finite K premises;
the two widened forward clauses are not derived here. -/
namespace PASoundness.PAtoCompactSeededSpanMatrixWitness

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactPartialCompositionAtSource PASoundness.PAtoCompactCommonSourceSpanImages
open PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage PASoundness.PAtoCompactSeededSpanSeedSourceUnique
open PASoundness.PAtoCompactSeededSpanCleanEndpoints PASoundness.PAtoCompactFirstSpanPathOutside
open PASoundness.PAtoCompactFirstSpanTargetOutside PASoundness.PAtoCompactSeededSpanOrderFreshening

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def fixedBase : Formula := namedBoth (namedCandidate 0)
  (namedBoth (namedCandidate 8) (namedBoth (namedCandidate 40) (namedBoth (namedCandidate 41)
    (namedBoth (namedEither (.equal 40 0) (.member 0 40))
      (namedBoth (namedEither (.equal 41 8) (.member 8 41))
        (namedBoth outsideGuard (namedBoth targetGuard (namedBoth seedClean seedOriginal))))))))

def guard : Formula := namedBoth firstClause (namedBoth secondClause (namedBoth (namedCandidate 1)
  (namedBoth seedBijection (namedBoth firstBijection (namedBoth secondBijection
    (namedBoth fixedBase (namedBoth PASoundness.PAtoCompactFirstSuffixOrderWiden.suffixOrder
      PASoundness.PAtoCompactSecondSuffixOrderWiden.suffixOrder)))))))

def output : Formula := .ex 9 PASoundness.PAtoCompactSeededSpanConditionalMatrix.targetMatrix

/-- Construct graph9 with the collector and use that same witness for the
target matrix; the fixed guard is checked vacuous at graph label 9. -/
def seeded_matrix_witness : KDerivation (imp guard.encode output.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [guard.encode]
  have hg : Context Γ guard.encode := .head _ _
  have hf : Context Γ firstClause.encode := Context.conjunctionLeft hg
  have hr := Context.conjunctionRight hg
  have hs : Context Γ secondClause.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hc : Context Γ (namedCandidate 1).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hseed : Context Γ seedBijection.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hb1 : Context Γ firstBijection.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hb2 : Context Γ secondBijection.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hbase : Context Γ fixedBase.encode := Context.conjunctionLeft hr
  have horders := Context.conjunctionRight hr
  have hex : Context Γ (existsCode 9 fullSpan.encode) :=
    .mp hc (.mp hs (.mp hf (.closed PASoundness.PAtoCompactSeededSpanInduction.common_source_span)))
  have hlocal : Context (fullSpan.encode :: Γ)
      PASoundness.PAtoCompactSeededSpanConditionalMatrix.targetMatrix.encode := by
    let Δ := fullSpan.encode :: Γ
    have hspan : Context Δ fullSpan.encode := .head _ _
    have hseed' : Context Δ seedBijection.encode := .under hseed _
    have hb1' : Context Δ firstBijection.encode := .under hb1 _
    have hb2' : Context Δ secondBijection.encode := .under hb2 _
    have hbase' : Context Δ fixedBase.encode := .under hbase _
    have ho' := Context.under horders fullSpan.encode
    have hfullBase : Context Δ PASoundness.PAtoCompactSeededSpanMatrixFromSeedOrder.baseGuard.encode :=
      Context.conjunctionIntro hspan hbase'
    have hconsolidated : Context Δ PASoundness.PAtoCompactSeededSpanMatrixConsolidated.guard.encode :=
      Context.conjunctionIntro hseed' (Context.conjunctionIntro hb1' (Context.conjunctionIntro hb2'
        (Context.conjunctionIntro hfullBase ho')))
    exact .mp hconsolidated (.closed PASoundness.PAtoCompactSeededSpanMatrixConsolidated.matrix_from_consolidated_guard)
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 9 h)) := by
    intro h hh
    have he : h = guard.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 9 guard (by decide)
  have hall := Context.generalize 9 hv (Context.deduction hlocal)
  simpa only [output,Formula.encode] using PASoundness.PAtoCompactTransitiveWitness.exists_map_context hall hex

theorem seeded_matrix_witness_certificate : theoremCode (certificate seeded_matrix_witness) =
    imp guard.encode output.encode := certificate_correct seeded_matrix_witness

end PASoundness.PAtoCompactSeededSpanMatrixWitness

#print axioms PASoundness.PAtoCompactSeededSpanMatrixWitness.fixedBase
#print axioms PASoundness.PAtoCompactSeededSpanMatrixWitness.guard
#print axioms PASoundness.PAtoCompactSeededSpanMatrixWitness.output
#print axioms PASoundness.PAtoCompactSeededSpanMatrixWitness.seeded_matrix_witness
#print axioms PASoundness.PAtoCompactSeededSpanMatrixWitness.seeded_matrix_witness_certificate
