import PASoundness.PAtoCompactCommonSourceSpanInversePath
import PASoundness.PAtoCompactRestrictedInverseFirst

/-! Specialize the existing restricted inverse matrix to common-source span
path labels. Both inverse directions remain literal K antecedents; this module
does not construct the inverse graph or assume either image is a candidate. -/
namespace PASoundness.PAtoCompactCommonSourceSpanInverseRestriction

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactRestrictedInverseFirst PASoundness.PAtoCompactCommonSourceSpanInversePath
open PASoundness.PAtoCompactFreeVacuity

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def forwardBody : Formula := .imp (namedBoth (.member 0 3) (.member 1 2))
  (.imp (graphFormula 14 2 3) (graphFormula 6 3 2))
private def backwardBody : Formula := .imp (namedBoth (.member 0 3) (.member 1 4))
  (.imp (graphFormula 6 3 4) (graphFormula 14 4 3))

def inverseForward : Formula := .all 3 (.all 2 forwardBody)
def inverseBackward : Formula := .all 3 (.all 4 backwardBody)
def inverseMatrix : Formula := namedBoth inverseForward inverseBackward

/-- The literal existing restricted inverse matrix after moving its original
forward graph to 14, swapping source 0 and 1 through fresh name 25, and
placing the inverse graph at 6. -/
def renamedRestriction : Formula := replace 7 6 (replace 25 1 (replace 1 0
  (replace 0 25 (replace 6 14 restrictedInverseMatrix))))

theorem restriction_alignment : renamedRestriction = inverseMatrix := by decide

private def forwardBody5 : Formula := replace 2 5 forwardBody
private def forwardAfter3 : Formula := replace 3 2 forwardBody5
private def backwardAfter3 : Formula := replace 3 2 backwardBody

private theorem forward_alpha_body : replace 3 2 (.all 5 forwardBody5) =
    .all 5 forwardAfter3 := by decide
private theorem forward_final : replace 5 4 forwardAfter3 =
    .imp (namedBoth (.member 0 2) (.member 1 4))
      (.imp (graphFormula 14 4 2) (graphFormula 6 2 4)) := by decide
private theorem backward_alpha_body : replace 3 2 (.all 4 backwardBody) =
    .all 4 backwardAfter3 := by decide
private theorem backward_final : backwardAfter3 =
    .imp (namedBoth (.member 0 2) (.member 1 4))
      (.imp (graphFormula 6 2 4) (graphFormula 14 4 2)) := by decide

private def forward_at_point : KDerivation (imp inverseForward.encode
    (imp (both (member 0 2) (member 1 4))
      (imp (graphFormula 14 4 2).encode (graphFormula 6 2 4).encode))) := by
  have ha := (universalAlpha 2 5 forwardBody (by decide) (by decide) (by decide)).1
  have houter := allCongr 3 ha
  have h3 := universalInstance 3 2 (.all 5 forwardBody5) (by decide) (by decide) (by decide)
  rw [forward_alpha_body] at h3
  have h5 := universalInstance 5 4 forwardAfter3 (by decide) (by decide) (by decide)
  rw [forward_final] at h5
  have h := compose houter (compose h3 h5)
  simpa [inverseForward, forwardBody5, Formula.encode, namedBoth, Formula.not, both, neg] using h

private def backward_at_point : KDerivation (imp inverseBackward.encode
    (imp (both (member 0 2) (member 1 4))
      (imp (graphFormula 6 2 4).encode (graphFormula 14 4 2).encode))) := by
  have h3 := universalInstance 3 2 (.all 4 backwardBody) (by decide) (by decide) (by decide)
  rw [backward_alpha_body] at h3
  have h4 := allSpecialize 4 backwardAfter3 (by decide)
  rw [backward_final] at h4
  have h := compose h3 h4
  simpa [inverseBackward, Formula.encode, namedBoth, Formula.not, both, neg] using h

/-- The supplied existing inverse matrix proves the exact two path-edge
transfers, uniformly over source and common-input members. -/
def restricted_inverse_correspondence : KDerivation
    (imp renamedRestriction.encode inverseCorrespondence.encode) := by
  rw [restriction_alignment]
  let Γ := [inverseMatrix.encode]
  have hm : Context Γ inverseMatrix.encode := .head _ _
  have hf : Context Γ inverseForward.encode := Context.conjunctionLeft hm
  have hb : Context Γ inverseBackward.encode := Context.conjunctionRight hm
  have hp : Context Γ inversePoint.encode := by
    apply Context.deduction
    let D := both (member 0 2) (member 1 4)
    let Δ := [D,inverseMatrix.encode]
    have hd : Context Δ D := .head _ _
    have hforward : Context Δ (imp (graphFormula 14 4 2).encode (graphFormula 6 2 4).encode) :=
      .mp hd (.mp (.under hf D) (.closed forward_at_point))
    have hbackward : Context Δ (imp (graphFormula 6 2 4).encode (graphFormula 14 4 2).encode) :=
      .mp hd (.mp (.under hb D) (.closed backward_at_point))
    exact Context.conjunctionIntro hforward hbackward
  have hv4 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 4 h)) := by
    intro h hh
    have he : h = inverseMatrix.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 4 inverseMatrix (by decide)
  have hv2 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 2 h)) := by
    intro h hh
    have he : h = inverseMatrix.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 2 inverseMatrix (by decide)
  have hall : Context Γ inverseCorrespondence.encode := by
    simpa only [inverseCorrespondence, Formula.encode] using
      Context.generalize 2 hv2 (Context.generalize 4 hv4 hp)
  exact Context.closeEmpty (Context.deduction hall)

theorem restricted_inverse_correspondence_certificate :
    theoremCode (certificate restricted_inverse_correspondence) =
      imp renamedRestriction.encode inverseCorrespondence.encode :=
  certificate_correct restricted_inverse_correspondence

end PASoundness.PAtoCompactCommonSourceSpanInverseRestriction

#print axioms PASoundness.PAtoCompactCommonSourceSpanInverseRestriction.inverseForward
#print axioms PASoundness.PAtoCompactCommonSourceSpanInverseRestriction.inverseBackward
#print axioms PASoundness.PAtoCompactCommonSourceSpanInverseRestriction.inverseMatrix
#print axioms PASoundness.PAtoCompactCommonSourceSpanInverseRestriction.renamedRestriction
#print axioms PASoundness.PAtoCompactCommonSourceSpanInverseRestriction.restriction_alignment
#print axioms PASoundness.PAtoCompactCommonSourceSpanInverseRestriction.restricted_inverse_correspondence
#print axioms PASoundness.PAtoCompactCommonSourceSpanInverseRestriction.restricted_inverse_correspondence_certificate
