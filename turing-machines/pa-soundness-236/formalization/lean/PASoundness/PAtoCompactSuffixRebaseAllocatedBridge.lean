import PASoundness.PAtoCompactSuffixRebaseTargetFrame
import PASoundness.PAtoCompactSuffixRebaseFilterAlpha
import PASoundness.PAtoCompactSuffixEquivalentAlphaEndpoints
import PASoundness.PAtoCompactSuffixRebaseMatrixAlpha

/-! Fixed-label bridge from the original outer isomorphism matrices and two
actual suffix filters to the allocated equivalence of those suffixes. The
matched cut edge and all cut-membership hypotheses remain explicit. -/
namespace PASoundness.PAtoCompactSuffixRebaseAllocatedBridge
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactSuffixRebaseMatrixAlpha
open PASoundness.PAtoCompactSuffixRebaseFilterAlpha PASoundness.PAtoCompactSuffixEquivalentAlphaEndpoints
open PASoundness.PAtoCompactSuffixRebaseRenamedFrame PASoundness.PAtoCompactSuffixRebaseTargetFrame
set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Assuming one supplied order/bijection graph 60, the matched proper-cut
edge 33→41, both corresponding memberships and the actual old/new suffix
filters, K derives allocated equivalence of suffixes 34 and 38. All names
are syntactic labels; the objects they denote may coincide. -/
noncomputable def allocated_suffix_equivalent : KDerivation
    (imp (relabel orderFormula).encode
      (imp suffixFormula.encode
        (imp targetSuffix.encode
          (imp (member 32 33)
            (imp (member 8 41)
              (imp (graphFormula 60 33 41).encode
                (imp (relabel bijectionFormula).encode (PASoundness.PAtoCompactTermTranslation.equivAt 100 34 38).encode))))))) := by
  let O := (relabel orderFormula).encode
  let S := suffixFormula.encode
  let T := targetSuffix.encode
  let C := member 32 33
  let D := member 8 41
  let E := (graphFormula 60 33 41).encode
  let B := (relabel bijectionFormula).encode
  let Γ := [B,E,D,C,T,S,O]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hb : Context Γ B := .head _ _
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have ho : Context Γ O := .hypothesis (by simp [Γ])
  have ho' : Context Γ (relabel orderAlpha).encode := .mp ho (.closed order_relabel.1)
  have hb' : Context Γ (relabel bijectionAlpha).encode := .mp hb (.closed bijection_relabel.1)
  have hs' : Context Γ sourceFilter42.encode := .mp hs (.closed source_suffix_to_filter42)
  have ht' : Context Γ targetFilter43.encode := .mp ht (.closed target_suffix_to_filter43)
  have hf : KDerivation targetFrame.encode := by
    have h := renamed_frame_proof
    rw [renamed_frame_shape] at h
    exact h
  have hq : Context Γ alphaEndpoint.encode := by
    have hp : Context Γ targetFrame.encode := .closed hf
    change Context Γ (imp (relabel orderAlpha).encode (imp sourceFilter42.encode
      (imp targetFilter43.encode (imp C (imp D (imp E
        (imp (relabel bijectionAlpha).encode alphaEndpoint.encode))))))) at hp
    exact .mp hb' (.mp he (.mp hd (.mp hc (.mp ht' (.mp hs' (.mp ho' hp))))))
  exact .mp hq (.closed alpha_to_allocated_endpoint)

theorem allocated_suffix_equivalent_certificate :
    theoremCode (certificate allocated_suffix_equivalent) =
      imp (relabel orderFormula).encode
        (imp suffixFormula.encode
          (imp targetSuffix.encode
            (imp (member 32 33)
              (imp (member 8 41)
                (imp (graphFormula 60 33 41).encode
                  (imp (relabel bijectionFormula).encode (PASoundness.PAtoCompactTermTranslation.equivAt 100 34 38).encode)))))) :=
  certificate_correct allocated_suffix_equivalent

end PASoundness.PAtoCompactSuffixRebaseAllocatedBridge

#print axioms PASoundness.PAtoCompactSuffixRebaseAllocatedBridge.allocated_suffix_equivalent
#print axioms PASoundness.PAtoCompactSuffixRebaseAllocatedBridge.allocated_suffix_equivalent_certificate
