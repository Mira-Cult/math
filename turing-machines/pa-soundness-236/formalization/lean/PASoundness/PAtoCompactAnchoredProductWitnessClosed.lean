import PASoundness.PAtoCompactAnchoredProductWitnessPackage
import PASoundness.PAtoCompactLiteralCutSuffix40

/-! Construct a literal suffix together with the SAME clean old, suffix map,
and row graphs. This does not establish any new product matrix clause. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAnchoredProductWitnessClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactLiteralCutBaseSyntax
open PASoundness.PAtoCompactAnchoredProductWitnessPackage
open PASoundness.PAtoCompactLiteralCutSuffix40

/-- The cut/suffix data and all three graph witnesses share the actual suffix
name 40 and the actual old and suffix-map graph witnesses. -/
noncomputable def anchored_product_witness : KDerivation
    (imp (literalCutAt 100 32 31 45).encode (imp inputs.encode anchoredResult.encode)) := by
  apply package_of_suffix
  simpa [suffixData,rawBody] using literal_cut_suffix40

theorem anchored_product_witness_certificate :
    theoremCode (certificate anchored_product_witness) =
      imp (literalCutAt 100 32 31 45).encode (imp inputs.encode anchoredResult.encode) :=
  certificate_correct _
end PASoundness.PAtoCompactAnchoredProductWitnessClosed
#print axioms PASoundness.PAtoCompactAnchoredProductWitnessClosed.anchored_product_witness
#print axioms PASoundness.PAtoCompactAnchoredProductWitnessClosed.anchored_product_witness_certificate
