import PASoundness.PAtoCompactCleanMatrixData
import PASoundness.PAtoCompactRestrictionEdgeEquivalence

/-! The supplied endpoint filter yields uniform edge equivalence for guarded
endpoints. This is finite K proof data, not graph existence, matrix transfer,
or a quotient theorem. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCleanEdges
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCleanMatrixData PASoundness.PAtoCompactRestrictionEdgeEquivalence
open PASoundness.PAtoCompactRestrictionFilterVacuity

/-- The exact filter graph implies the uniform comparison at names 28,29.
The quantified source and target guards remain explicit. -/
def guarded_edges : KDerivation (imp filterCode guardedEdges.encode) := by
  have hp : KDerivation (imp filterCode
      (imp (member 0 28) (imp (member 1 29)
        (both (imp (PASoundness.PAtoCompactOrderIsomorphism.graphFormula 10 28 29).encode
                   (PASoundness.PAtoCompactOrderIsomorphism.graphFormula 6 28 29).encode)
          (imp (PASoundness.PAtoCompactOrderIsomorphism.graphFormula 6 28 29).encode
               (PASoundness.PAtoCompactOrderIsomorphism.graphFormula 10 28 29).encode))))) :=
    restricted_edge_iff 10 6 17 0 1 28 29 (by decide)
  have hv28 : KDerivation (imp filterCode (allCode 28 filterCode)) :=
    restriction_filter_vacuity 10 6 17 0 1 28 (by decide)
  have hv29 : KDerivation (imp filterCode (allCode 29 filterCode)) :=
    restriction_filter_vacuity 10 6 17 0 1 29 (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  have hh := Context.mp (Context.head [] filterCode) (.closed hp)
  have h29 := Context.generalize 29 (by
    intro z hz
    have he : z = filterCode := by simpa using hz
    subst z
    exact hv29) hh
  have h28 := Context.generalize 28 (by
    intro z hz
    have he : z = filterCode := by simpa using hz
    subst z
    exact hv28) h29
  exact h28

theorem guarded_edges_certificate : theoremCode (certificate guarded_edges) =
    imp filterCode guardedEdges.encode := certificate_correct guarded_edges

end PASoundness.PAtoCompactCleanEdges

#print axioms PASoundness.PAtoCompactCleanEdges.guarded_edges
#print axioms PASoundness.PAtoCompactCleanEdges.guarded_edges_certificate
