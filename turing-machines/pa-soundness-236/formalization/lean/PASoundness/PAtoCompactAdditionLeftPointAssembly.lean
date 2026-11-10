import PASoundness.PAtoCompactAdditionOldSourceClosed
import PASoundness.PAtoCompactAdditionTopWitnessUnequal
import PASoundness.PAtoCompactSuccessorInjective

/-! Pointwise assembly for the source side of the unequal-top addition graph
extension. The equality transport of the top witness is an explicit finite K
proof-data input. The old witness is extracted from the supplied bijection.
This is neither a quantified bijection clause nor addition totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionLeftPointAssembly
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactAdditionSuccessorGraphClean
open PASoundness.PAtoCompactAdditionOldSourceWitness PASoundness.PAtoCompactAdditionOldSourceClosed
open PASoundness.PAtoCompactAdditionTopWitnessUnequal PASoundness.PAtoCompactSuccessorInjective
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The pointwise source case, assuming the explicit top-witness transport. -/
def source_point
    (topTransport : KDerivation (imp (equal 2 31)
      (imp (existsCode 3 topSourceWitness.encode) (existsCode 3 newBody.encode)))) :
    KDerivation (imp oldBijection.encode (imp oldClean.encode
      (imp (adjoinCode 6 11 9 16) (imp (pairFormula 11 31 32).encode
        (imp (adjoinCode 34 32 40 41) (imp (successorCode 31 38 39)
          (imp (member 38 2) (existsCode 3 newBody.encode)))))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 38 2, successorCode 31 38 39, adjoinCode 34 32 40 41,
    (pairFormula 11 31 32).encode, adjoinCode 6 11 9 16, oldClean.encode, oldBijection.encode]
  have hm : Context Γ (member 38 2) := .head _ _
  have hs : Context Γ (successorCode 31 38 39) := .hypothesis (by simp [Γ])
  have ht : Context Γ (adjoinCode 34 32 40 41) := .hypothesis (by simp [Γ])
  have hp : Context Γ (pairFormula 11 31 32).encode := .hypothesis (by simp [Γ])
  have hg : Context Γ (adjoinCode 6 11 9 16) := .hypothesis (by simp [Γ])
  have hc : Context Γ oldClean.encode := .hypothesis (by simp [Γ])
  have hb : Context Γ oldBijection.encode := .hypothesis (by simp [Γ])
  have cases : Context Γ (either (equal 2 31) (member 31 2)) :=
    .mp hm (.mp hs (.closed (successor_inspect 31 38 39 2 (by decide) (by decide) (by decide))))
  apply Context.disjunctionElim cases
  · have he : Context (equal 2 31 :: Γ) (equal 2 31) := .head _ _
    have hw : Context Γ (existsCode 3 topSourceWitness.encode) :=
      .mp hc (.mp hp (.mp hg (.mp ht (.closed top_source_witness))))
    exact .mp (.under hw _) (.mp he (.closed topTransport))
  · have ho : Context (member 31 2 :: Γ) (member 31 2) := .head _ _
    exact .mp ho (.mp (.under ht _) (.mp (.under hp _) (.mp (.under hg _)
      (.mp (.under hc _) (.mp (.under hb _) (.closed old_source_case))))))

theorem source_point_certificate
    (topTransport : KDerivation (imp (equal 2 31)
      (imp (existsCode 3 topSourceWitness.encode) (existsCode 3 newBody.encode)))) :
    theoremCode (certificate (source_point topTransport)) =
      imp oldBijection.encode (imp oldClean.encode
        (imp (adjoinCode 6 11 9 16) (imp (pairFormula 11 31 32).encode
          (imp (adjoinCode 34 32 40 41) (imp (successorCode 31 38 39)
            (imp (member 38 2) (existsCode 3 newBody.encode))))))) :=
  certificate_correct (source_point topTransport)
end PASoundness.PAtoCompactAdditionLeftPointAssembly
#print axioms PASoundness.PAtoCompactAdditionLeftPointAssembly.source_point
#print axioms PASoundness.PAtoCompactAdditionLeftPointAssembly.source_point_certificate
