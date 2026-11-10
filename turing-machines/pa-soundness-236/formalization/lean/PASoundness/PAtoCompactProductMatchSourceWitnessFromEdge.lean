import PASoundness.PAtoCompactProductMatchPathUnique
import PASoundness.PAtoCompactSuccGraphOutputLift

/-! Reconstruct the source product's reverse witness at displayed factor
coordinates and output. This is a local ingredient for reverse matching;
no product match or reverse-totality theorem is asserted here. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchSourceWitnessFromEdge

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactSuccGraphOutputLift PASoundness.PAtoCompactMulTermTransportWitness
open PASoundness.PAtoCompactProductMatchPointWitness PASoundness.PAtoCompactProductMatchPointUnique
open PASoundness.PAtoCompactProductMatchPathUnique

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def rivalUnique : Formula := replace 31 51 (replace 30 50 reverseUnique)
def edgeGuard : Formula := namedBoth productMatrix (namedBoth (.member 0 30)
  (namedBoth (.member 1 31) (namedBoth (.member 2 32) (tripleFormula 30 31 32))))

/-- From a supplied source product matrix and displayed guarded triple,
recover its full reverse witness at those exact coordinates. -/
def source_witness : KDerivation (imp productMatrix.encode (imp (member 0 30)
    (imp (member 1 31) (imp (member 2 32) (imp (tripleFormula 30 31 32).encode
      selectedReverseBody.encode))))) := by
  have h7 := universalInstance 7 30 (.all 8 rivalUnique) (by decide) (by decide) (by decide)
  have hs7 : replace 7 30 (.all 8 rivalUnique) = .all 8 (replace 7 30 rivalUnique) := by decide
  rw [hs7] at h7
  have h8 := universalInstance 8 31 (replace 7 30 rivalUnique)
    (by decide) (by decide) (by decide)
  have hs8 : replace 8 31 (replace 7 30 rivalUnique) =
      .imp (namedBoth (.member 0 30) (namedBoth (.member 1 31) (tripleFormula 30 31 32)))
        (namedBoth (.equal 30 50) (.equal 31 51)) := by decide
  rw [hs8] at h8
  have he₁ := (equalityReplace 50 30 rivalReverse (by decide) (by decide)).1
  have he₂ := (equalityReplace 51 31 (replace 50 30 rivalReverse) (by decide) (by decide)).1
  have heshape : replace 51 31 (replace 50 30 rivalReverse) = selectedReverseBody := by decide
  rw [heshape] at he₂
  have hpoint : KDerivation (imp edgeGuard.encode (imp rivalReverse.encode selectedReverseBody.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [rivalReverse.encode,edgeGuard.encode]
    have hr : Context Γ rivalReverse.encode := .head _ _
    have hg : Context Γ edgeGuard.encode := .hypothesis (by simp [Γ])
    have hr' : Context Γ (both (member 0 50) (both (member 1 51)
        (both (tripleFormula 50 51 32).encode (allCode 7 (allCode 8 rivalUnique.encode))))) := by
      simpa [rival_reverse_shape, rivalUnique, namedBoth, Formula.not, Formula.encode, both, neg] using hr
    have hg' : Context Γ (both productMatrix.encode (both (member 0 30)
        (both (member 1 31) (both (member 2 32) (tripleFormula 30 31 32).encode)))) := by
      simpa [edgeGuard, namedBoth, Formula.not, Formula.encode, both, neg] using hg
    have hsource : Context Γ (both (member 0 30) (both (member 1 31)
        (tripleFormula 30 31 32).encode)) :=
      Context.conjunctionIntro (Context.conjunctionLeft (Context.conjunctionRight hg'))
        (Context.conjunctionIntro (Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hg')))
          (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg')))))
    have hu := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hr'))
    have heq' := Context.mp hsource (Context.mp (Context.mp hu (.closed h7)) (.closed h8))
    have heq : Context Γ (both (equal 30 50) (equal 31 51)) := by
      simpa [namedBoth, Formula.not, Formula.encode, both, neg] using heq'
    have ha : Context Γ (equal 50 30) := Context.eqSymm (Context.conjunctionLeft heq)
    have hb : Context Γ (equal 51 31) := Context.eqSymm (Context.conjunctionRight heq)
    have hr₁ := Context.mp hr (Context.mp ha (.closed he₁))
    exact .mp hr₁ (.mp hb (.closed he₂))
  have helim₅₁ := guarded_exists_left 51 edgeGuard.encode rivalReverse.encode selectedReverseBody.encode
    (edgeGuard.vacuity 51 (by decide)) (selectedReverseBody.vacuity 51 (by decide)) hpoint
  have helim₅₀ := guarded_exists_left 50 edgeGuard.encode (existsCode 51 rivalReverse.encode)
    selectedReverseBody.encode (edgeGuard.vacuity 50 (by decide))
    (selectedReverseBody.vacuity 50 (by decide)) helim₅₁
  have ha := two_exists_alpha selectedReverseBody 30 31 50 51
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hshape : replace 31 51 (replace 30 50 selectedReverseBody) = rivalReverse := by rfl
  rw [hshape] at ha
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(tripleFormula 30 31 32).encode,member 2 32,member 1 31,member 0 30,productMatrix.encode]
  have he : Context Γ (tripleFormula 30 31 32).encode := .head _ _
  have hz : Context Γ (member 2 32) := .hypothesis (by simp [Γ])
  have hy : Context Γ (member 1 31) := .hypothesis (by simp [Γ])
  have hx : Context Γ (member 0 30) := .hypothesis (by simp [Γ])
  have hm : Context Γ productMatrix.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ edgeGuard.encode := by
    have h := Context.conjunctionIntro hm (Context.conjunctionIntro hx
      (Context.conjunctionIntro hy (Context.conjunctionIntro hz he)))
    simpa [edgeGuard, namedBoth, Formula.not, Formula.encode, both, neg] using h
  have hw := Context.mp hz (Context.mp hm (.closed reverse_coordinates))
  have hw' : Context Γ (existsCode 50 (existsCode 51 rivalReverse.encode)) := by
    simpa [Formula.encode] using Context.mp hw (.closed ha.forward)
  exact .mp hw' (.mp hg (.closed helim₅₀))

theorem source_witness_certificate : theoremCode (certificate source_witness) =
    imp productMatrix.encode (imp (member 0 30) (imp (member 1 31)
      (imp (member 2 32) (imp (tripleFormula 30 31 32).encode selectedReverseBody.encode)))) := certificate_correct _

end PASoundness.PAtoCompactProductMatchSourceWitnessFromEdge

#print axioms PASoundness.PAtoCompactProductMatchSourceWitnessFromEdge.source_witness
#print axioms PASoundness.PAtoCompactProductMatchSourceWitnessFromEdge.source_witness_certificate
