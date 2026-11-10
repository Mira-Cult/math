import PASoundness.PAtoCompactFirstSuffixPreimage
import PASoundness.PAtoCompactSecondSuffixImage
import PASoundness.PAtoCompactSeededSpanEdgeIntro
import PASoundness.PAtoCompactFirstSpanTargetOutside
import PASoundness.PAtoCompactAdjunction

/-! Forward coverage for a specified point already known to lie in source
suffix31. The source-to-suffix bijections, target suffix filter, actual whole
membership and full-prefix seeded invariant are explicit. Both selected
witnesses are retained through K existential elimination. -/
namespace PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactFilterInstantiation
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactSeededSpanBase
open PASoundness.PAtoCompactCommonSourceSpanBase PASoundness.PAtoCompactSeededSpanEdgeIntro
open PASoundness.PAtoCompactFirstSuffixPreimage PASoundness.PAtoCompactSecondSuffixImage
open PASoundness.PAtoCompactFirstSpanTargetOutside

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def firstBijection : Formula := PASoundness.PAtoCompactFirstSuffixInverseSelected.suffixBijection
def secondBijection : Formula := PASoundness.PAtoCompactSecondSuffixForwardSelected.suffixBijection
def fullSpan : Formula := replace 10 1 seededSpan
private def fullBody : Formula := replace 10 1 spanPathBody
private def fullPath : Formula := .ex 4 fullBody
def outputBody : Formula := namedBoth (.member 8 3) (graphFormula 9 2 3)
def output : Formula := .ex 3 outputBody
def guard : Formula := namedBoth firstBijection (namedBoth secondBijection
  (namedBoth fullSpan (namedBoth targetFilter (namedBoth (.member 0 2) (.member 31 2)))))

private theorem full_path_shape : replace 10 1 spanPath = fullPath := by decide
private theorem full_body_at42 : replace 4 42 fullBody = namedBoth (.member 1 42)
  (namedBoth (.member 1 42) (namedBoth (graphFormula 6 42 2) (graphFormula 7 42 3))) := by decide

private def full_path_intro : KDerivation (imp fullSpan.encode
    (imp (both (member 0 2) (member 8 3)) (imp fullPath.encode (graphFormula 9 2 3).encode))) := by
  let frame : Formula := .imp seededSpan (.imp (namedBoth (.member 0 2) (.member 8 3))
    (.imp spanPath (graphFormula 9 2 3)))
  have hbase : KDerivation frame.encode := by
    simpa only [frame,namedBoth,Formula.encode,CompactProof.both,CompactProof.neg] using path_edge_intro
  have h := replace_derivation 10 1 frame (by decide) (by decide) hbase
  have ha : replace 10 1 frame = .imp fullSpan (.imp (namedBoth (.member 0 2) (.member 8 3))
      (.imp fullPath (graphFormula 9 2 3))) := by decide
  rw [ha] at h
  exact h

private def target_contained_at_three : KDerivation (imp targetFilter.encode
    (imp (member 38 3) (member 8 3))) := by
  have hi := filter_at 8 38 35 3 targetPredicate (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hcode : targetFilter.encode = filterGraph 8 38 35 (neg (member 41 35)) := by rfl
  have hi' : KDerivation (imp targetFilter.encode
      (both (imp (member 38 3) (both (member 8 3) (neg (member 41 3))))
        (imp (both (member 8 3) (neg (member 41 3))) (member 38 3)))) := by
    simpa [hcode,targetPredicate,Formula.not,Formula.encode,replace,rename,neg] using hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 38 3,targetFilter.encode]
  have hm : Context Γ (member 38 3) := .head _ _
  have hf : Context Γ targetFilter.encode := .hypothesis (by simp [Γ])
  have hb : Context Γ (both (imp (member 38 3) (both (member 8 3) (neg (member 41 3))))
      (imp (both (member 8 3) (neg (member 41 3))) (member 38 3))) := .mp hf (.closed hi')
  have hp : Context Γ (imp (member 38 3) (both (member 8 3) (neg (member 41 3)))) := Context.conjunctionLeft hb
  have ht : Context Γ (both (member 8 3) (neg (member 41 3))) := .mp hm hp
  exact Context.conjunctionLeft ht

/-- A source-suffix point has an output graph edge into whole8 under the
literal full-prefix invariant, both bijections and target suffix filter. -/
def suffix_forward_coverage : KDerivation (imp guard.encode output.encode) := by
  have hintro := exists_variable_intro 4 42 fullBody (by decide) (by decide) (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [guard.encode]
  have hg : Context Γ guard.encode := .head _ _
  have hf : Context Γ firstBijection.encode := Context.conjunctionLeft hg
  have hr := Context.conjunctionRight hg
  have hs : Context Γ secondBijection.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hspan : Context Γ fullSpan.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hfilter : Context Γ targetFilter.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hwhole : Context Γ (member 0 2) := Context.conjunctionLeft hr
  have hsuffix : Context Γ (member 31 2) := Context.conjunctionRight hr
  have hpre : Context Γ preimage.encode := .mp hsuffix (.mp hf (.closed first_suffix_preimage))
  have himage : Context (preimageBody.encode :: Γ) image.encode := by
    let Δ := preimageBody.encode :: Γ
    have hp : Context Δ preimageBody.encode := .head _ _
    have hsource : Context Δ (member 1 42) := Context.conjunctionLeft hp
    have hs' : Context Δ secondBijection.encode := .under hs preimageBody.encode
    exact .mp hsource (.mp hs' (.closed second_suffix_image))
  have hlocal : Context (imageBody.encode :: preimageBody.encode :: Γ) output.encode := by
    let Δ := imageBody.encode :: preimageBody.encode :: Γ
    have him : Context Δ imageBody.encode := .head _ _
    have hpr : Context Δ preimageBody.encode := .under (.head Γ preimageBody.encode) imageBody.encode
    have hsource : Context Δ (member 1 42) := Context.conjunctionLeft hpr
    have he6 : Context Δ (graphFormula 6 42 2).encode := Context.conjunctionRight hpr
    have htargetSuffix : Context Δ (member 38 3) := Context.conjunctionLeft him
    have he7 : Context Δ (graphFormula 7 42 3).encode := Context.conjunctionRight him
    have hfilt : Context Δ targetFilter.encode := .under (.under hfilter preimageBody.encode) imageBody.encode
    have hw : Context Δ (member 0 2) := .under (.under hwhole preimageBody.encode) imageBody.encode
    have hsp : Context Δ fullSpan.encode := .under (.under hspan preimageBody.encode) imageBody.encode
    have htarget : Context Δ (member 8 3) := .mp htargetSuffix (.mp hfilt (.closed target_contained_at_three))
    have hbody : Context Δ (replace 4 42 fullBody).encode := by
      rw [full_body_at42]
      exact Context.conjunctionIntro hsource (Context.conjunctionIntro hsource (Context.conjunctionIntro he6 he7))
    have hpath : Context Δ fullPath.encode := .mp hbody (.closed hintro)
    have hedge : Context Δ (graphFormula 9 2 3).encode :=
      .mp hpath (.mp (Context.conjunctionIntro hw htarget) (.mp hsp (.closed full_path_intro)))
    have hout : Context Δ outputBody.encode := Context.conjunctionIntro htarget hedge
    exact .mp hout (.closed (existsIntroduce 3 outputBody (by decide)))
  have hv3 : ∀ h, h ∈ preimageBody.encode :: Γ → KDerivation (imp h (allCode 3 h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases he : h = preimageBody.encode
    · subst h; exact free_vacuity 3 preimageBody (by decide)
    · have he' : h = guard.encode := hh.resolve_left he
      subst h; exact free_vacuity 3 guard (by decide)
  have hmid : Context (preimageBody.encode :: Γ) output.encode := Context.existsElim
    (free_vacuity 3 output (by decide)) (Context.generalize 3 hv3 (Context.deduction hlocal)) himage
  have hv42 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 42 h)) := by
    intro h hh
    have he : h = guard.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 42 guard (by decide)
  exact Context.existsElim (free_vacuity 42 output (by decide))
    (Context.generalize 42 hv42 (Context.deduction hmid)) hpre

theorem suffix_forward_coverage_certificate : theoremCode (certificate suffix_forward_coverage) =
    imp guard.encode output.encode := certificate_correct suffix_forward_coverage

end PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage

#print axioms PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage.firstBijection
#print axioms PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage.secondBijection
#print axioms PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage.fullSpan
#print axioms PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage.outputBody
#print axioms PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage.output
#print axioms PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage.guard
#print axioms PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage.suffix_forward_coverage
#print axioms PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage.suffix_forward_coverage_certificate
