import PASoundness.PAtoCompactFirstSuffixForwardSelected
import PASoundness.PAtoCompactSecondSuffixInverseSelected

/-! Discharge the four selected local uniqueness tests from the two actual
suffix bijections and their stored-clean graphs. The selected witnesses,
endpoint memberships and actual graph edges remain explicit. -/
namespace PASoundness.PAtoCompactSelectedPathUniquenessFromBijections

open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactSeededSpanPointUniqueness PASoundness.PAtoCompactSeededSpanSelectedPathUniqueness
open PASoundness.PAtoCompactSuffixCleanGraphGuard PASoundness.PAtoCompactFirstSpanTargetOutside

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def firstBijection : PASoundness.CompactNamed.Formula := PASoundness.PAtoCompactFirstSuffixInverseSelected.suffixBijection
def secondBijection : PASoundness.CompactNamed.Formula := PASoundness.PAtoCompactSecondSuffixForwardSelected.suffixBijection

/-- Actual suffix bijections and clean graphs supply all four local tests;
the selected path guard still carries the same two witnesses and edges. -/
def selected_uniqueness_from_bijections : KDerivation (imp firstBijection.encode
    (imp storedClean.encode (imp secondBijection.encode (imp targetClean.encode
      (imp selectedGuard pointUniqueness))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [selectedGuard,targetClean.encode,secondBijection.encode,storedClean.encode,firstBijection.encode]
  have hg : Context Γ selectedGuard := .head _ _
  have htc : Context Γ targetClean.encode := .hypothesis (by simp [Γ])
  have htb : Context Γ secondBijection.encode := .hypothesis (by simp [Γ])
  have hsc : Context Γ storedClean.encode := .hypothesis (by simp [Γ])
  have hsb : Context Γ firstBijection.encode := .hypothesis (by simp [Γ])
  have hfi : Context Γ firstInverse := .mp hsc (.mp hsb
    (.closed PASoundness.PAtoCompactFirstSuffixInverseSelected.selected_first_inverse))
  have hsf : Context Γ secondForward := .mp htc (.mp htb
    (.closed PASoundness.PAtoCompactSecondSuffixForwardSelected.selected_second_forward))
  have hsi : Context Γ secondInverse := .mp htc (.mp htb
    (.closed PASoundness.PAtoCompactSecondSuffixInverseSelected.selected_second_inverse))
  have hff : Context Γ firstForward := .mp hsc (.mp hsb
    (.closed PASoundness.PAtoCompactFirstSuffixForwardSelected.selected_first_forward))
  exact .mp hff (.mp hsi (.mp hsf (.mp hfi (.mp hg (.closed selected_path_uniqueness)))))

theorem selected_uniqueness_from_bijections_certificate :
    theoremCode (certificate selected_uniqueness_from_bijections) =
      imp firstBijection.encode (imp storedClean.encode (imp secondBijection.encode
        (imp targetClean.encode (imp selectedGuard pointUniqueness)))) :=
  certificate_correct selected_uniqueness_from_bijections

end PASoundness.PAtoCompactSelectedPathUniquenessFromBijections

#print axioms PASoundness.PAtoCompactSelectedPathUniquenessFromBijections.firstBijection
#print axioms PASoundness.PAtoCompactSelectedPathUniquenessFromBijections.secondBijection
#print axioms PASoundness.PAtoCompactSelectedPathUniquenessFromBijections.selected_uniqueness_from_bijections
#print axioms PASoundness.PAtoCompactSelectedPathUniquenessFromBijections.selected_uniqueness_from_bijections_certificate
