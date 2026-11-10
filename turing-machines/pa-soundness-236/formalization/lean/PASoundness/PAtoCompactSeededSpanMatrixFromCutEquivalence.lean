import PASoundness.PAtoCompactSeededSpanMatrixFromWholeCandidates
import PASoundness.PAtoCompactSeededSpanCleanSeedWitness

/-! Obtain the seed graph from the supplied cut equivalence and keep that
same graph in all seed premises used by the matrix construction. -/
namespace PASoundness.PAtoCompactSeededSpanMatrixFromCutEquivalence

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactPartialCompositionAtSource PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage
open PASoundness.PAtoCompactFirstSpanPathOutside PASoundness.PAtoCompactFirstSpanTargetOutside
open PASoundness.PAtoCompactSeededSpanCutCandidate PASoundness.PAtoCompactSeededSpanCleanSeedWitness
open PASoundness.PAtoCompactSeededSpanCleanEndpoints PASoundness.PAtoCompactSeededSpanSeedSourceUnique
open PASoundness.PAtoCompactSeededSpanOrderFreshening

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def fixedBase : Formula := namedBoth (namedCandidate 0) (namedBoth (namedCandidate 8)
  (namedBoth sourceRelation (namedBoth targetRelation (namedBoth outsideGuard targetGuard))))
def guard : Formula := namedBoth (namedCandidate 1) (namedBoth seedEquivalence
  (namedBoth firstBijection (namedBoth secondBijection
    (namedBoth fixedBase (namedBoth PASoundness.PAtoCompactFirstSuffixOrderWiden.suffixOrder
      PASoundness.PAtoCompactSecondSuffixOrderWiden.suffixOrder)))))

/-- The cut equivalence constructs the seed graph; the resulting target
matrix graph remains existential and retains the other explicit premises. -/
def matrix_from_cut_equivalence : KDerivation (imp guard.encode
    PASoundness.PAtoCompactSeededSpanMatrixWitness.output.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [guard.encode]
  have hg : Context Γ guard.encode := .head _ _
  have hc1 : Context Γ (namedCandidate 1).encode := Context.conjunctionLeft hg
  have hr := Context.conjunctionRight hg
  have heq : Context Γ seedEquivalence.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hb1 : Context Γ firstBijection.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hb2 : Context Γ secondBijection.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hb : Context Γ fixedBase.encode := Context.conjunctionLeft hr
  have ho := Context.conjunctionRight hr
  have hex : Context Γ PASoundness.PAtoCompactSeededSpanCleanSeedWitness.output.encode :=
    .mp heq (.closed clean_seed_witness)
  have hlocal : Context (seedMatrix.encode :: Γ)
      PASoundness.PAtoCompactSeededSpanMatrixWitness.output.encode := by
    let Δ := seedMatrix.encode :: Γ
    have hseed : Context Δ seedMatrix.encode := .head _ _
    have hpair := Context.conjunctionLeft hseed
    have hbij : Context Δ seedBijection.encode := Context.conjunctionLeft hpair
    have horder : Context Δ seedOriginal.encode := Context.conjunctionRight hpair
    have hclean : Context Δ seedClean.encode := Context.conjunctionRight hseed
    have hb' : Context Δ fixedBase.encode := .under hb _
    have hc0 : Context Δ (namedCandidate 0).encode := Context.conjunctionLeft hb'
    have hr := Context.conjunctionRight hb'
    have hc8 : Context Δ (namedCandidate 8).encode := Context.conjunctionLeft hr
    have hr := Context.conjunctionRight hr
    have hr0 : Context Δ sourceRelation.encode := Context.conjunctionLeft hr
    have hr := Context.conjunctionRight hr
    have hr8 : Context Δ targetRelation.encode := Context.conjunctionLeft hr
    have hr := Context.conjunctionRight hr
    have hsource : Context Δ outsideGuard.encode := Context.conjunctionLeft hr
    have htarget : Context Δ targetGuard.encode := Context.conjunctionRight hr
    have hbase : Context Δ PASoundness.PAtoCompactSeededSpanMatrixFromWholeCandidates.fixedBase.encode :=
      Context.conjunctionIntro hc0 (Context.conjunctionIntro hc8 (Context.conjunctionIntro hr0
        (Context.conjunctionIntro hr8 (Context.conjunctionIntro hsource (Context.conjunctionIntro htarget
          (Context.conjunctionIntro hclean horder))))))
    have hc1' : Context Δ (namedCandidate 1).encode := .under hc1 _
    have hb1' : Context Δ firstBijection.encode := .under hb1 _
    have hb2' : Context Δ secondBijection.encode := .under hb2 _
    have ho' := Context.under ho seedMatrix.encode
    have hguard : Context Δ PASoundness.PAtoCompactSeededSpanMatrixFromWholeCandidates.guard.encode :=
      Context.conjunctionIntro hc1' (Context.conjunctionIntro hbij (Context.conjunctionIntro hb1'
        (Context.conjunctionIntro hb2' (Context.conjunctionIntro hbase ho'))))
    exact .mp hguard (.closed PASoundness.PAtoCompactSeededSpanMatrixFromWholeCandidates.matrix_from_whole_candidates)
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 14 h)) := by
    intro h hh
    have he : h = guard.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 14 guard (by decide)
  have hall := Context.generalize 14 hv (Context.deduction hlocal)
  exact Context.existsElim
    (free_vacuity 14 PASoundness.PAtoCompactSeededSpanMatrixWitness.output (by decide)) hall hex

theorem matrix_from_cut_equivalence_certificate : theoremCode (certificate matrix_from_cut_equivalence) =
    imp guard.encode PASoundness.PAtoCompactSeededSpanMatrixWitness.output.encode :=
  certificate_correct matrix_from_cut_equivalence

end PASoundness.PAtoCompactSeededSpanMatrixFromCutEquivalence

#print axioms PASoundness.PAtoCompactSeededSpanMatrixFromCutEquivalence.fixedBase
#print axioms PASoundness.PAtoCompactSeededSpanMatrixFromCutEquivalence.guard
#print axioms PASoundness.PAtoCompactSeededSpanMatrixFromCutEquivalence.matrix_from_cut_equivalence
#print axioms PASoundness.PAtoCompactSeededSpanMatrixFromCutEquivalence.matrix_from_cut_equivalence_certificate
