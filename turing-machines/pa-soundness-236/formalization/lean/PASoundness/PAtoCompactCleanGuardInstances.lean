import PASoundness.PAtoCompactCleanBijectionInstance

/-! Additional guarded edge instance for the exact order matrix. All graph
comparison and domain-guard formulas remain explicit hypotheses in K. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCleanGuardInstances
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactCleanMatrixData PASoundness.PAtoCompactCleanBijectionInstance

/-- Guarded comparison at source 4 and target 5. -/
def instance_45 : KDerivation (imp guardedEdges.encode (edgePoint 4 5).encode) := by
  have h1 := CompactNamed.universalInstance 28 4 (.all 29 (edgePoint 28 29))
    (by decide) (by decide) (by decide)
  have hr1 : CompactNamed.replace 28 4 (.all 29 (edgePoint 28 29)) =
      .all 29 (edgePoint 4 29) := by decide
  rw [hr1] at h1
  have h2 := CompactNamed.universalInstance 29 5 (edgePoint 4 29)
    (by decide) (by decide) (by decide)
  have hr2 : CompactNamed.replace 29 5 (edgePoint 4 29) = edgePoint 4 5 := by decide
  rw [hr2] at h2
  exact compose h1 h2

theorem instance_45_certificate : theoremCode (certificate instance_45) =
    imp guardedEdges.encode (edgePoint 4 5).encode := certificate_correct instance_45

end PASoundness.PAtoCompactCleanGuardInstances

#print axioms PASoundness.PAtoCompactCleanGuardInstances.instance_45
#print axioms PASoundness.PAtoCompactCleanGuardInstances.instance_45_certificate
