import PASoundness.PAtoCompactSecondSuffixPreimage
import PASoundness.PAtoCompactFirstSuffixImage
import PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage
import PASoundness.PAtoCompactFirstSpanPathOutside

/-! Reverse coverage for a specified point already known to lie in target
suffix38. The two suffix bijections, source suffix filter, actual whole
membership and full-prefix invariant are explicit. The common-source and
output witnesses are retained through K existential elimination. -/
namespace PASoundness.PAtoCompactSeededSpanSuffixReverseCoverage

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactFilterInstantiation
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactSeededSpanBase
open PASoundness.PAtoCompactCommonSourceSpanBase PASoundness.PAtoCompactSeededSpanEdgeIntro
open PASoundness.PAtoCompactSecondSuffixPreimage PASoundness.PAtoCompactFirstSuffixImage
open PASoundness.PAtoCompactFirstSpanPathOutside

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def firstBijection : Formula := PASoundness.PAtoCompactFirstSuffixInverseSelected.suffixBijection
def secondBijection : Formula := PASoundness.PAtoCompactSecondSuffixForwardSelected.suffixBijection
def fullSpan : Formula := replace 10 1 seededSpan
private def fullBody : Formula := replace 10 1 spanPathBody
private def fullPath : Formula := .ex 4 fullBody
def outputBody : Formula := namedBoth (.member 0 2) (graphFormula 9 2 3)
def output : Formula := .ex 2 outputBody
def guard : Formula := namedBoth firstBijection (namedBoth secondBijection
  (namedBoth fullSpan (namedBoth suffixFilter (namedBoth (.member 8 3) (.member 38 3)))))

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

private def source_contained_at_two : KDerivation (imp suffixFilter.encode
    (imp (member 31 2) (member 0 2))) := by
  have hi := filter_at 0 31 35 2 suffixPredicate (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hcode : suffixFilter.encode = filterGraph 0 31 35 (neg (member 40 35)) := by rfl
  have hi' : KDerivation (imp suffixFilter.encode
      (both (imp (member 31 2) (both (member 0 2) (neg (member 40 2))))
        (imp (both (member 0 2) (neg (member 40 2))) (member 31 2)))) := by
    simpa [hcode,suffixPredicate,Formula.not,Formula.encode,replace,rename,neg] using hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 31 2,suffixFilter.encode]
  have hm : Context Γ (member 31 2) := .head _ _
  have hf : Context Γ suffixFilter.encode := .hypothesis (by simp [Γ])
  have hb : Context Γ (both (imp (member 31 2) (both (member 0 2) (neg (member 40 2))))
      (imp (both (member 0 2) (neg (member 40 2))) (member 31 2))) := .mp hf (.closed hi')
  have hp : Context Γ (imp (member 31 2) (both (member 0 2) (neg (member 40 2)))) := Context.conjunctionLeft hb
  have ht : Context Γ (both (member 0 2) (neg (member 40 2))) := .mp hm hp
  exact Context.conjunctionLeft ht

/-- A target-suffix point has a graph9 preimage in whole0 under the literal
full-prefix invariant, both bijections and source suffix filter. -/
def suffix_reverse_coverage : KDerivation (imp guard.encode output.encode) := by
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
  have hfilter : Context Γ suffixFilter.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hwhole : Context Γ (member 8 3) := Context.conjunctionLeft hr
  have hsuffix : Context Γ (member 38 3) := Context.conjunctionRight hr
  have hpre : Context Γ preimage.encode := .mp hsuffix (.mp hs (.closed second_suffix_preimage))
  have himage : Context (preimageBody.encode :: Γ) image.encode := by
    let Δ := preimageBody.encode :: Γ
    have hp : Context Δ preimageBody.encode := .head _ _
    have hsource : Context Δ (member 1 42) := Context.conjunctionLeft hp
    have hf' : Context Δ firstBijection.encode := .under hf preimageBody.encode
    exact .mp hsource (.mp hf' (.closed first_suffix_image))
  have hlocal : Context (imageBody.encode :: preimageBody.encode :: Γ) output.encode := by
    let Δ := imageBody.encode :: preimageBody.encode :: Γ
    have him : Context Δ imageBody.encode := .head _ _
    have hpr : Context Δ preimageBody.encode := .under (.head Γ preimageBody.encode) imageBody.encode
    have hsource : Context Δ (member 1 42) := Context.conjunctionLeft hpr
    have he7 : Context Δ (graphFormula 7 42 3).encode := Context.conjunctionRight hpr
    have hsourceSuffix : Context Δ (member 31 2) := Context.conjunctionLeft him
    have he6 : Context Δ (graphFormula 6 42 2).encode := Context.conjunctionRight him
    have hfilt : Context Δ suffixFilter.encode := .under (.under hfilter preimageBody.encode) imageBody.encode
    have hw : Context Δ (member 8 3) := .under (.under hwhole preimageBody.encode) imageBody.encode
    have hsp : Context Δ fullSpan.encode := .under (.under hspan preimageBody.encode) imageBody.encode
    have hsourceWhole : Context Δ (member 0 2) := .mp hsourceSuffix (.mp hfilt (.closed source_contained_at_two))
    have hbody : Context Δ (replace 4 42 fullBody).encode := by
      rw [full_body_at42]
      exact Context.conjunctionIntro hsource (Context.conjunctionIntro hsource (Context.conjunctionIntro he6 he7))
    have hpath : Context Δ fullPath.encode := .mp hbody (.closed hintro)
    have hedge : Context Δ (graphFormula 9 2 3).encode :=
      .mp hpath (.mp (Context.conjunctionIntro hsourceWhole hw) (.mp hsp (.closed full_path_intro)))
    have hout : Context Δ outputBody.encode := Context.conjunctionIntro hsourceWhole hedge
    exact .mp hout (.closed (existsIntroduce 2 outputBody (by decide)))
  have hv2 : ∀ h, h ∈ preimageBody.encode :: Γ → KDerivation (imp h (allCode 2 h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases he : h = preimageBody.encode
    · subst h; exact free_vacuity 2 preimageBody (by decide)
    · have he' : h = guard.encode := hh.resolve_left he
      subst h; exact free_vacuity 2 guard (by decide)
  have hmid : Context (preimageBody.encode :: Γ) output.encode := Context.existsElim
    (free_vacuity 2 output (by decide)) (Context.generalize 2 hv2 (Context.deduction hlocal)) himage
  have hv42 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 42 h)) := by
    intro h hh
    have he : h = guard.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 42 guard (by decide)
  exact Context.existsElim (free_vacuity 42 output (by decide))
    (Context.generalize 42 hv42 (Context.deduction hmid)) hpre

theorem suffix_reverse_coverage_certificate : theoremCode (certificate suffix_reverse_coverage) =
    imp guard.encode output.encode := certificate_correct suffix_reverse_coverage

end PASoundness.PAtoCompactSeededSpanSuffixReverseCoverage

#print axioms PASoundness.PAtoCompactSeededSpanSuffixReverseCoverage.firstBijection
#print axioms PASoundness.PAtoCompactSeededSpanSuffixReverseCoverage.secondBijection
#print axioms PASoundness.PAtoCompactSeededSpanSuffixReverseCoverage.fullSpan
#print axioms PASoundness.PAtoCompactSeededSpanSuffixReverseCoverage.outputBody
#print axioms PASoundness.PAtoCompactSeededSpanSuffixReverseCoverage.output
#print axioms PASoundness.PAtoCompactSeededSpanSuffixReverseCoverage.guard
#print axioms PASoundness.PAtoCompactSeededSpanSuffixReverseCoverage.suffix_reverse_coverage
#print axioms PASoundness.PAtoCompactSeededSpanSuffixReverseCoverage.suffix_reverse_coverage_certificate
