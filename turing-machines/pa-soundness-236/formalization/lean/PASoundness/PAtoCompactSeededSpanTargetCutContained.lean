import PASoundness.PAtoCompactSeededSpanSeedForwardCoverage
import PASoundness.PAtoCompactCandidateTransitiveTests
import PASoundness.PAtoCompactTransitiveClosure
import PASoundness.PAtoCompactPartialCompositionAtSource

/-! The target cut is contained in its whole when the supplied target whole
is a candidate and the cut is equal to or a member of it. This derives the
cut-containment premise used in seed-side forward coverage; it does not
construct either object or prove outside-cut coverage. -/
namespace PASoundness.PAtoCompactSeededSpanTargetCutContained

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactCandidateTransitiveTests
open PASoundness.PAtoCompactPartialCompositionAtSource PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactSeededSpanSeedForwardCoverage

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def guard : Formula := namedBoth (namedCandidate 8) (namedEither (.equal 41 8) (.member 8 41))

/-- The literal candidate transitivity and actual cut relation imply that
every member of cut41 is a member of whole8. -/
def target_cut_contained : KDerivation (imp guard.encode cutContained.encode) := by
  have htrans := candidate_transitive_tests 8 37 32 33 34 30 35 13 36 42 43 (by decide)
  have hchain := transitive_chain 8 42 43 41 5 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [guard.encode]
  have hg : Context Γ guard.encode := .head _ _
  have hc : Context Γ (namedCandidate 8).encode := Context.conjunctionLeft hg
  have hr : Context Γ (either (equal 41 8) (member 8 41)) := Context.conjunctionRight hg
  have ht : Context Γ (transitiveCode 8 42 43) := .mp hc (.closed htrans)
  have hp : Context Γ (imp (member 41 5) (member 8 5)) := by
    apply Context.deduction
    let Δ := [member 41 5,guard.encode]
    have hm : Context Δ (member 41 5) := .head _ _
    have hr' : Context Δ (either (equal 41 8) (member 8 41)) := .under hr (member 41 5)
    have ht' : Context Δ (transitiveCode 8 42 43) := .under ht (member 41 5)
    apply Context.disjunctionElim hr'
    · let Θ := equal 41 8 :: Δ
      have he : Context Θ (equal 41 8) := .head _ _
      have hm' : Context Θ (member 41 5) := .under hm (equal 41 8)
      exact .mp hm' (.mp he (.closed (memberLeftEquality 41 8 5)))
    · let Θ := member 8 41 :: Δ
      have he : Context Θ (member 8 41) := .head _ _
      have hm' : Context Θ (member 41 5) := .under hm (member 8 41)
      have ht'' : Context Θ (transitiveCode 8 42 43) := .under ht' (member 8 41)
      exact .mp hm' (.mp he (.mp ht'' (.closed hchain)))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 5 h)) := by
    intro h hh
    have he : h = guard.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 5 guard (by decide)
  have hall := Context.generalize 5 hv hp
  simpa only [cutContained,Formula.encode] using hall

theorem target_cut_contained_certificate : theoremCode (certificate target_cut_contained) =
    imp guard.encode cutContained.encode := certificate_correct target_cut_contained

end PASoundness.PAtoCompactSeededSpanTargetCutContained

#print axioms PASoundness.PAtoCompactSeededSpanTargetCutContained.guard
#print axioms PASoundness.PAtoCompactSeededSpanTargetCutContained.target_cut_contained
#print axioms PASoundness.PAtoCompactSeededSpanTargetCutContained.target_cut_contained_certificate
