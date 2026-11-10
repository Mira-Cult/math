import PASoundness.PAtoCompactSuffixGraphQuotientAlignment
import PASoundness.PAtoCompactAlphaMapOne
import PASoundness.PAtoCompactScopedActiveReplace
import PASoundness.PAtoCompactStagedEquivalenceAligned

/-! Binder preparation and endpoint relocation for the suffix quotient
formula. The imported suffix graph construction is not proved here. The
three alpha steps provide finite K proof equivalences; the endpoints move
through a temporary name before being installed at 34 and 38. -/
namespace PASoundness.PAtoCompactSuffixEquivalentAlphaEndpoints
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactAlphaMapOne PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactStagedEquivalenceAlpha PASoundness.PAtoCompactStagedEquivalenceAligned
open PASoundness.PAtoCompactSuffixGraphQuotientAlignment
set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Move binder names that are free coordinates in the outer transport. -/
def alpha2 : Formula := mapNames (rename 2 102) suffixEquivalent
def alpha5 : Formula := mapNames (rename 5 105) alpha2
def alpha6 : Formula := mapNames (rename 6 106) alpha5

/-- Explicit K proof equivalence for those three bound-name changes. -/
noncomputable def alpha_equivalent : ProofEquiv suffixEquivalent alpha6 := by
  have h2 : ProofEquiv suffixEquivalent alpha2 :=
    alpha_map_one 2 102 suffixEquivalent (by decide) (by decide) (by decide) (by decide)
  have h5 : ProofEquiv alpha2 alpha5 :=
    alpha_map_one 5 105 alpha2 (by decide) (by decide) (by decide) (by decide)
  have h6 : ProofEquiv alpha5 alpha6 :=
    alpha_map_one 6 106 alpha5 (by decide) (by decide) (by decide) (by decide)
  exact h2.trans (h5.trans h6)

/-- The old target 41 is moved away before the cut image is installed at 41
by the enclosing transport. These endpoint transformations preserve the
same source and target objects. -/
def rawStage1 : Formula := replace 41 70 suffixEquivalent
def rawStage2 : Formula := replace 40 34 rawStage1
def rawEndpoint : Formula := replace 70 38 rawStage2

def alphaStage1 : Formula := replace 41 70 alpha6
def alphaStage2 : Formula := replace 40 34 alphaStage1
def alphaEndpoint : Formula := replace 70 38 alphaStage2

/-- K proof transport between the binder-prepared and literal suffix
isomorphisms after relocation. The endpoint objects may coincide. -/
noncomputable def endpoint_equivalent :
    KDerivation (imp alphaEndpoint.encode rawEndpoint.encode) ×
    KDerivation (imp rawEndpoint.encode alphaEndpoint.encode) := by
  have h := alpha_equivalent
  have r1 := replace_implications 41 70 suffixEquivalent alpha6
    (by decide) (by decide) (by decide) (by decide) h.forward h.backward
  have r2 := replace_implications 40 34 rawStage1 alphaStage1
    (by decide) (by decide) (by decide) (by decide)
    (by simpa only [rawStage1,alphaStage1] using r1.1)
    (by simpa only [rawStage1,alphaStage1] using r1.2)
  have r3 := replace_implications 70 38 rawStage2 alphaStage2
    (by decide) (by decide) (by decide) (by decide)
    (by simpa only [rawStage2,alphaStage2] using r2.1)
    (by simpa only [rawStage2,alphaStage2] using r2.2)
  exact ⟨by simpa only [rawEndpoint,alphaEndpoint] using r3.2,
    by simpa only [rawEndpoint,alphaEndpoint] using r3.1⟩

/-- After capture-safe relocation the literal endpoint syntax is the
independently prepared staging of source 34 and target 38. -/
theorem raw_endpoint_shape : rawEndpoint = rawStaged 34 38 := by decide

/-- The alpha-prepared suffix equivalence entails the allocated equivalence
used by the term-graph translation. No graph existence is assumed. -/
noncomputable def alpha_to_allocated_endpoint : KDerivation
    (imp alphaEndpoint.encode (equivAt 100 34 38).encode) := by
  have ha := endpoint_equivalent.1
  rw [raw_endpoint_shape] at ha
  exact compose ha (staged_to_allocated 34 38 (by decide) (by decide)
    (by decide) (by decide) (by decide))

theorem alpha_to_allocated_endpoint_certificate :
    theoremCode (certificate alpha_to_allocated_endpoint) =
      imp alphaEndpoint.encode (equivAt 100 34 38).encode := certificate_correct _

end PASoundness.PAtoCompactSuffixEquivalentAlphaEndpoints

#print axioms PASoundness.PAtoCompactSuffixEquivalentAlphaEndpoints.alpha_equivalent
#print axioms PASoundness.PAtoCompactSuffixEquivalentAlphaEndpoints.endpoint_equivalent
#print axioms PASoundness.PAtoCompactSuffixEquivalentAlphaEndpoints.raw_endpoint_shape
#print axioms PASoundness.PAtoCompactSuffixEquivalentAlphaEndpoints.alpha_to_allocated_endpoint
#print axioms PASoundness.PAtoCompactSuffixEquivalentAlphaEndpoints.alpha_to_allocated_endpoint_certificate
