import PASoundness.PAtoCompactMultiplicationSuffixInjective41
import PASoundness.PAtoCompactMultiplicationSuffixCleanEdges

/-! Literal K inverse uniqueness for a clean supplied suffix map. This is a
pointwise conditional graph property; no pair-representative uniqueness,
product-graph construction or multiplication totality is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationSuffixCleanInjective41
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactMultiplicationSuffixInjective41
open PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A clean suffix bijection has at most one source for any represented
output. Cleanliness derives the source guards from the two edges and the
target guard from either edge. -/
def clean_inverse_unique : KDerivation (imp suffixClean.encode
    (imp suffixBijection.encode (imp (graphFormula 6 41 5).encode
      (imp (graphFormula 6 8 5).encode (equal 41 8))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 6 8 5).encode,(graphFormula 6 41 5).encode,
    suffixBijection.encode,suffixClean.encode]
  have he8 : Context Γ (graphFormula 6 8 5).encode := .head _ _
  have he4 : Context Γ (graphFormula 6 41 5).encode := .hypothesis (by simp [Γ])
  have hb : Context Γ suffixBijection.encode := .hypothesis (by simp [Γ])
  have hc : Context Γ suffixClean.encode := .hypothesis (by simp [Γ])
  have hp4 := Context.mp he4 (Context.mp hc (.closed (clean_endpoints 41 5 (by decide))))
  have hp8 := Context.mp he8 (Context.mp hc (.closed (clean_endpoints 8 5 (by decide))))
  have hs4 : Context Γ (member 31 41) := Context.conjunctionLeft hp4
  have hs8 : Context Γ (member 31 8) := Context.conjunctionLeft hp8
  have ht : Context Γ (member 40 5) := Context.conjunctionRight hp4
  exact .mp he8 (.mp he4 (.mp hs8 (.mp hs4 (.mp ht (.mp hb (.closed inverse_unique))))))

theorem clean_inverse_unique_certificate : theoremCode (certificate clean_inverse_unique) =
    imp suffixClean.encode (imp suffixBijection.encode (imp (graphFormula 6 41 5).encode
      (imp (graphFormula 6 8 5).encode (equal 41 8)))) := certificate_correct clean_inverse_unique
end PASoundness.PAtoCompactMultiplicationSuffixCleanInjective41
#print axioms PASoundness.PAtoCompactMultiplicationSuffixCleanInjective41.clean_inverse_unique
#print axioms PASoundness.PAtoCompactMultiplicationSuffixCleanInjective41.clean_inverse_unique_certificate
