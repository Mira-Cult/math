import PASoundness.PAtoCompactSuffixGraphEquivalent
import PASoundness.PAtoCompactSuffixRebaseMatrixAlpha
import PASoundness.PAtoCompactSuffixEquivalentAlphaEndpoints

/-! Assemble the componentwise binder freshening needed before active-name
replacement in the suffix isomorphism proof. The original fixed graph, both
filters and the matched cut edge remain explicit. The alpha frame does not
itself relocate free names or prove addition output transport. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuffixRebaseAlphaFrame
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactFilterInstantiation
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactSuffixBoundaryPoint
open PASoundness.PAtoCompactSuffixGraphQuotientAlignment PASoundness.PAtoCompactSuffixGraphEquivalent
open PASoundness.PAtoCompactSuffixRebaseMatrixAlpha PASoundness.PAtoCompactSuffixEquivalentAlphaEndpoints
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The actual relative-complement filters in named syntax. -/
def sourceFilterNamed : Formula :=
  .all 42 (namedFilterBody 0 40 42 (Formula.member 2 42).not)
def targetFilterNamed : Formula :=
  .all 43 (namedFilterBody 1 41 43 (Formula.member 5 43).not)

theorem source_filter_code : sourceFilterNamed.encode = sourceFilter := by rfl
theorem target_filter_code : targetFilterNamed.encode = targetFilter := by rfl

/-- The full conditional suffix-equivalence frame at the original free names.
Its order, bijection and conclusion are parameters to permit capture-safe
componentwise alpha conversion. -/
def frame (order bijection quotient : Formula) : Formula :=
  .imp order (.imp sourceFilterNamed (.imp targetFilterNamed
    (.imp (.member 0 2) (.imp (.member 1 5) (.imp (graphFormula 6 2 5)
      (.imp bijection quotient))))))

def originalFrame : Formula := frame orderFormula bijectionFormula suffixEquivalent

def alphaFrame : Formula := frame orderAlpha bijectionAlpha alpha6

/-- K proof equivalence is composed contravariantly through the antecedents
and covariantly through the conclusion. The same filter and graph formulas
are used on both sides. -/
def frame_equiv {o o' b b' q q' : Formula}
    (ho : ProofEquiv o o') (hb : ProofEquiv b b') (hq : ProofEquiv q q') :
    ProofEquiv (frame o b q) (frame o' b' q') := by
  unfold frame
  exact ProofEquiv.implication ho
    (ProofEquiv.implication (ProofEquiv.refl sourceFilterNamed)
      (ProofEquiv.implication (ProofEquiv.refl targetFilterNamed)
        (ProofEquiv.implication (ProofEquiv.refl (.member 0 2))
          (ProofEquiv.implication (ProofEquiv.refl (.member 1 5))
            (ProofEquiv.implication (ProofEquiv.refl (graphFormula 6 2 5))
              (ProofEquiv.implication hb hq))))))

/-- Original suffix-equivalence proof in its exact named frame. -/
noncomputable def original_frame_proof : KDerivation originalFrame.encode := by
  simpa only [originalFrame, frame, Formula.encode, source_filter_code, target_filter_code]
    using suffix_graph_equivalent

/-- A capture-safe alpha-prepared finite K proof: binders 2/5 in the order,
2 in the bijection and 2/5/6 in the suffix quotient are moved away from
free source labels. This leaves all original free variables unchanged. -/
noncomputable def alpha_frame_proof : KDerivation alphaFrame.encode := by
  have h : ProofEquiv originalFrame alphaFrame :=
    frame_equiv order_prepare bijection_prepare alpha_equivalent
  exact .mp original_frame_proof h.forward

theorem alpha_frame_certificate : theoremCode (certificate alpha_frame_proof) = alphaFrame.encode :=
  certificate_correct alpha_frame_proof

end PASoundness.PAtoCompactSuffixRebaseAlphaFrame

#print axioms PASoundness.PAtoCompactSuffixRebaseAlphaFrame.sourceFilterNamed
#print axioms PASoundness.PAtoCompactSuffixRebaseAlphaFrame.targetFilterNamed
#print axioms PASoundness.PAtoCompactSuffixRebaseAlphaFrame.source_filter_code
#print axioms PASoundness.PAtoCompactSuffixRebaseAlphaFrame.target_filter_code
#print axioms PASoundness.PAtoCompactSuffixRebaseAlphaFrame.frame
#print axioms PASoundness.PAtoCompactSuffixRebaseAlphaFrame.originalFrame
#print axioms PASoundness.PAtoCompactSuffixRebaseAlphaFrame.alphaFrame
#print axioms PASoundness.PAtoCompactSuffixRebaseAlphaFrame.frame_equiv
#print axioms PASoundness.PAtoCompactSuffixRebaseAlphaFrame.original_frame_proof
#print axioms PASoundness.PAtoCompactSuffixRebaseAlphaFrame.alpha_frame_proof
#print axioms PASoundness.PAtoCompactSuffixRebaseAlphaFrame.alpha_frame_certificate
