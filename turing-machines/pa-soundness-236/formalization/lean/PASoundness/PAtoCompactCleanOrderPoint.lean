import PASoundness.PAtoCompactCleanMatrixData

/-! Pointwise order-matrix transfer from a supplied guarded edge comparison.
The two comparison instances are explicit K proof-data arguments; no filter
existence, matrix transfer under quantifiers, or quotient law is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCleanOrderPoint
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCleanMatrixData PASoundness.PAtoCompactOrderIsomorphism

/-- The two graph-10 edges in the displayed pointwise order matrix. -/
def oldA : Nat := both (member 0 2) (both (member 0 4) (both (member 1 3)
  (both (member 1 5) (both (graphFormula 10 2 3).encode (graphFormula 10 4 5).encode))))

/-- The corresponding graph-6 edge and endpoint-guard conjunction. -/
def newA : Nat := both (member 0 2) (both (member 0 4) (both (member 1 3)
  (both (member 1 5) (both (graphFormula 6 2 3).encode (graphFormula 6 4 5).encode))))

def comparison : Nat := both (imp (member 4 2) (member 5 3)) (imp (member 5 3) (member 4 2))

/-- Pointwise edge comparison at the first order pair. -/
def guard23 : Nat := imp guardedEdges.encode (imp (member 0 2) (imp (member 1 3)
  (both (imp (graphFormula 10 2 3).encode (graphFormula 6 2 3).encode)
    (imp (graphFormula 6 2 3).encode (graphFormula 10 2 3).encode))))

/-- Pointwise edge comparison at the second order pair. -/
def guard45 : Nat := imp guardedEdges.encode (imp (member 0 4) (imp (member 1 5)
  (both (imp (graphFormula 10 4 5).encode (graphFormula 6 4 5).encode)
    (imp (graphFormula 6 4 5).encode (graphFormula 10 4 5).encode))))

/-- Given both explicitly supplied K instances of the uniform guarded-edge
comparison and the old pointwise order implication, derive the exact new
pointwise implication. Endpoint guards are used before replacing each edge. -/
def point_transfer (h23 : KDerivation guard23) (h45 : KDerivation guard45) :
    KDerivation (imp guardedEdges.encode (imp (imp oldA comparison) (imp newA comparison))) := by
  let G := guardedEdges.encode
  let O := imp oldA comparison
  let Γ := [newA,O,G]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hn : Context Γ newA := Context.head _ _
  have ho : Context Γ O := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hx2 : Context Γ (member 0 2) := Context.conjunctionLeft hn
  have hx4 : Context Γ (member 0 4) := Context.conjunctionLeft (Context.conjunctionRight hn)
  have hy3 : Context Γ (member 1 3) :=
    Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hn))
  have hy5 : Context Γ (member 1 5) := Context.conjunctionLeft
    (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hn)))
  have hg23 : Context Γ (graphFormula 6 2 3).encode := Context.conjunctionLeft
    (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hn))))
  have hg45 : Context Γ (graphFormula 6 4 5).encode := Context.conjunctionRight
    (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hn))))
  have hc23 : Context Γ (both (imp (graphFormula 10 2 3).encode (graphFormula 6 2 3).encode)
      (imp (graphFormula 6 2 3).encode (graphFormula 10 2 3).encode)) :=
    .mp hy3 (.mp hx2 (.mp hg (.closed h23)))
  have hc45 : Context Γ (both (imp (graphFormula 10 4 5).encode (graphFormula 6 4 5).encode)
      (imp (graphFormula 6 4 5).encode (graphFormula 10 4 5).encode)) :=
    .mp hy5 (.mp hx4 (.mp hg (.closed h45)))
  have ho23 : Context Γ (graphFormula 10 2 3).encode := .mp hg23 (Context.conjunctionRight hc23)
  have ho45 : Context Γ (graphFormula 10 4 5).encode := .mp hg45 (Context.conjunctionRight hc45)
  have hOld : Context Γ oldA := Context.conjunctionIntro hx2 (Context.conjunctionIntro hx4
    (Context.conjunctionIntro hy3 (Context.conjunctionIntro hy5 (Context.conjunctionIntro ho23 ho45))))
  exact .mp hOld ho

theorem point_transfer_certificate (h23 : KDerivation guard23) (h45 : KDerivation guard45) :
    theoremCode (certificate (point_transfer h23 h45)) =
      imp guardedEdges.encode (imp (imp oldA comparison) (imp newA comparison)) :=
  certificate_correct (point_transfer h23 h45)

end PASoundness.PAtoCompactCleanOrderPoint

#print axioms PASoundness.PAtoCompactCleanOrderPoint.point_transfer
#print axioms PASoundness.PAtoCompactCleanOrderPoint.point_transfer_certificate
