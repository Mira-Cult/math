import PASoundness.PAtoCompactSuccBijectionRight
import PASoundness.PAtoCompactSuccBijectionPremises
import PASoundness.PAtoCompactSuccRightTopCase
import PASoundness.PAtoCompactSuccEdgeSplit4Target28
import PASoundness.PAtoCompactSuccCleanEndpoint

/-! The top-target case of the supplied-clean-graph successor bijection,
using the checked edge split and old-graph endpoint theorem. All graph,
successor, pair and encoded irreflexivity premises remain in premisesCode;
no graph construction or quotient law is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccBijectionRightTopCompose
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactSuccCongruenceData PASoundness.PAtoCompactSuccBijectionPremises
open PASoundness.PAtoCompactSuccBijectionRight PASoundness.PAtoCompactSuccRightTopCase
open PASoundness.PAtoCompactSuccEdgeSplit4Target28 PASoundness.PAtoCompactSuccCleanEndpoint
open PASoundness.PAtoCompactOrderIsomorphism

/-- A clean old edge has its target in the old target domain. -/
def clean_target : KDerivation (imp cleanGraph (imp oldEdge (member 1 28))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldEdge,cleanGraph]
  have hc : Context Γ cleanGraph := .hypothesis (by simp [Γ])
  have he : Context Γ oldEdge := Context.head _ _
  have hboth : Context Γ (both (member 0 4) (member 1 28)) :=
    .mp he (.mp hc (.closed (clean_endpoints 4 28 (by decide))))
  exact Context.conjunctionRight hboth

/-- The exact shared premise conjunction discharges every top-target case
hypothesis; the target equality remains an explicit object-level antecedent. -/
def top_from_premises : KDerivation
    (imp premisesCode (imp (equal 28 1) (rightBody 28).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [equal 28 1,premisesCode]
  have hp : Context Γ premisesCode := .hypothesis (by simp [Γ])
  have ht : Context Γ (equal 28 1) := Context.head _ _
  have h1 := Context.conjunctionRight hp
  have hc : Context Γ cleanGraph := Context.conjunctionLeft h1
  have h2 := Context.conjunctionRight h1
  have hs : Context Γ sourceSuccessor := Context.conjunctionLeft h2
  have h3 := Context.conjunctionRight h2
  have h4 := Context.conjunctionRight h3
  have hpair : Context Γ newPair := Context.conjunctionLeft h4
  have h5 := Context.conjunctionRight h4
  have hgraph : Context Γ newGraph := Context.conjunctionLeft h5
  have h6 := Context.conjunctionRight h5
  have hirr : Context Γ targetIrreflexive := Context.conjunctionRight h6
  have htop := top_case edge_split_4_28 clean_target
  have hout : Context Γ (existsCode 2 witnessBody.encode) :=
    .mp ht (.mp hirr (.mp hc (.mp hpair (.mp hgraph (.mp hs (.closed htop))))))
  change Context Γ (existsCode 2 witnessBody.encode)
  exact hout

theorem top_from_premises_certificate : theoremCode (certificate top_from_premises) =
    imp premisesCode (imp (equal 28 1) (rightBody 28).encode) :=
  certificate_correct top_from_premises

end PASoundness.PAtoCompactSuccBijectionRightTopCompose

#print axioms PASoundness.PAtoCompactSuccBijectionRightTopCompose.top_from_premises
#print axioms PASoundness.PAtoCompactSuccBijectionRightTopCompose.top_from_premises_certificate
