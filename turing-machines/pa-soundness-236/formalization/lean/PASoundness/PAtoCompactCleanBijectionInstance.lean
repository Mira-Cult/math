import PASoundness.PAtoCompactCleanMatrixData

/-! Capture-safe fixed instances of supplied guarded edge equivalence for
bijection transfer. This constructs literal K proof data; it does not
establish edge equivalence, graph existence, or a quotient. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCleanBijectionInstance
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactCleanMatrixData

def edgePoint (a b : Nat) : Formula :=
  .imp (.member 0 a) (.imp (.member 1 b)
    (namedBoth (.imp (graphFormula 10 a b) (graphFormula 6 a b))
      (.imp (graphFormula 6 a b) (graphFormula 10 a b))))

theorem guarded_shape : guardedEdges = .all 28 (.all 29 (edgePoint 28 29)) := rfl

/-- Guarded comparison at source 2 and target 3. -/
def instance_23 : KDerivation (imp guardedEdges.encode (edgePoint 2 3).encode) := by
  have h1 := CompactNamed.universalInstance 28 2 (.all 29 (edgePoint 28 29))
    (by decide) (by decide) (by decide)
  have hr1 : CompactNamed.replace 28 2 (.all 29 (edgePoint 28 29)) =
      .all 29 (edgePoint 2 29) := by decide
  rw [hr1] at h1
  have h2 := CompactNamed.universalInstance 29 3 (edgePoint 2 29)
    (by decide) (by decide) (by decide)
  have hr2 : CompactNamed.replace 29 3 (edgePoint 2 29) = edgePoint 2 3 := by decide
  rw [hr2] at h2
  exact compose h1 h2

/-- Guarded comparison at source 2 and target 4. -/
def instance_24 : KDerivation (imp guardedEdges.encode (edgePoint 2 4).encode) := by
  have h1 := CompactNamed.universalInstance 28 2 (.all 29 (edgePoint 28 29))
    (by decide) (by decide) (by decide)
  have hr1 : CompactNamed.replace 28 2 (.all 29 (edgePoint 28 29)) =
      .all 29 (edgePoint 2 29) := by decide
  rw [hr1] at h1
  have h2 := CompactNamed.universalInstance 29 4 (edgePoint 2 29)
    (by decide) (by decide) (by decide)
  have hr2 : CompactNamed.replace 29 4 (edgePoint 2 29) = edgePoint 2 4 := by decide
  rw [hr2] at h2
  exact compose h1 h2

/-- Guarded comparison at source 4 and target 3. -/
def instance_43 : KDerivation (imp guardedEdges.encode (edgePoint 4 3).encode) := by
  have h1 := CompactNamed.universalInstance 28 4 (.all 29 (edgePoint 28 29))
    (by decide) (by decide) (by decide)
  have hr1 : CompactNamed.replace 28 4 (.all 29 (edgePoint 28 29)) =
      .all 29 (edgePoint 4 29) := by decide
  rw [hr1] at h1
  have h2 := CompactNamed.universalInstance 29 3 (edgePoint 4 29)
    (by decide) (by decide) (by decide)
  have hr2 : CompactNamed.replace 29 3 (edgePoint 4 29) = edgePoint 4 3 := by decide
  rw [hr2] at h2
  exact compose h1 h2

theorem instance_certificates :
    theoremCode (certificate instance_23) = imp guardedEdges.encode (edgePoint 2 3).encode ∧
    theoremCode (certificate instance_24) = imp guardedEdges.encode (edgePoint 2 4).encode ∧
    theoremCode (certificate instance_43) = imp guardedEdges.encode (edgePoint 4 3).encode :=
  ⟨certificate_correct instance_23, certificate_correct instance_24, certificate_correct instance_43⟩

end PASoundness.PAtoCompactCleanBijectionInstance

#print axioms PASoundness.PAtoCompactCleanBijectionInstance.instance_23
#print axioms PASoundness.PAtoCompactCleanBijectionInstance.instance_24
#print axioms PASoundness.PAtoCompactCleanBijectionInstance.instance_43
#print axioms PASoundness.PAtoCompactCleanBijectionInstance.instance_certificates
