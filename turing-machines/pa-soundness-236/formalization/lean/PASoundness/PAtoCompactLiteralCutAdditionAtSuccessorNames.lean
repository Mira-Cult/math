import PASoundness.PAtoCompactLiteralCutToAdditionFixed
import PASoundness.PAtoCompactPAAddSuccFiveRename
import PASoundness.PAtoCompactGuardBaseTransport

/-! Capture-safe relabeling of the fixed literal-cut-to-addition implication
for the first-factor multiplication-successor construction. The candidate
and literal cut are still explicit antecedents. -/
namespace PASoundness.PAtoCompactLiteralCutAdditionAtSuccessorNames

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactLiteralCutBaseSyntax
open PASoundness.PAtoCompactLiteralCutToAdditionFixed PASoundness.PAtoCompactPAAddSuccFiveRename
open PASoundness.PAtoCompactGuardBaseTransport

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def source : Formula := .imp (domainAt 100 30)
  (.imp (literalCutAt 300 30 31 32) (addAt 300 30 31 32))
private def target : Formula := .imp (domainAt 100 32)
  (.imp (literalCutAt 300 32 30 45) (addAt 300 32 30 45))

private theorem mapped_source : mapNames (mapping 32 30 45 38 45) source = target := by decide

/-- Reassign the three free parameter labels by staging, so the old product
label 32 becomes the first addition input and the output label 45 is kept.
The candidate premise still uses base 100. -/
def renamed_fixed : KDerivation target.encode := by
  have hsource : KDerivation source.encode := by
    simpa [source, Formula.encode] using allocated_fixed 300 (by decide)
  have hnames : source.names ⊆ Finset.range 500 := by decide
  have hfresh : ∀ i, i < 5 → 500+i ∉ source.names := by
    intro i _ hi
    have hlt : 500+i < 500 := Finset.mem_range.mp (hnames hi)
    omega
  have h := simultaneous_derivation source 500 32 30 45 38 45
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hfresh hsource
  rw [mapped_source] at h
  exact h

/-- Under the standard base-300 candidate guard for the old product, a
literal cut at the existing output implies ordinary addition at that same
output. No successor or product existence is asserted. -/
def for_successor_output : KDerivation
    (imp (domainAt 300 32).encode
      (imp (literalCutAt 300 32 30 45).encode (addAt 300 32 30 45).encode)) := by
  have hguard := domainAt_transport 300 100 32 (by decide) (by decide)
  have hrenamed : KDerivation (imp (domainAt 100 32).encode
      (imp (literalCutAt 300 32 30 45).encode (addAt 300 32 30 45).encode)) := by
    simpa [target, Formula.encode] using renamed_fixed
  exact compose hguard hrenamed

theorem for_successor_output_certificate :
    theoremCode (certificate for_successor_output) =
      imp (domainAt 300 32).encode
        (imp (literalCutAt 300 32 30 45).encode (addAt 300 32 30 45).encode) :=
  certificate_correct _

end PASoundness.PAtoCompactLiteralCutAdditionAtSuccessorNames

#print axioms PASoundness.PAtoCompactLiteralCutAdditionAtSuccessorNames.renamed_fixed
#print axioms PASoundness.PAtoCompactLiteralCutAdditionAtSuccessorNames.for_successor_output
#print axioms PASoundness.PAtoCompactLiteralCutAdditionAtSuccessorNames.for_successor_output_certificate
