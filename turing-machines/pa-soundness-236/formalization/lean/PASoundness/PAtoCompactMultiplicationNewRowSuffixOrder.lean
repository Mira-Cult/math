import PASoundness.PAtoCompactSuccCongruenceOrderAlpha
import PASoundness.PAtoCompactZeroSuccessor

/-! Capture-safe instantiation of a supplied suffix graph's order clause at
both directed pairs of product-row points. Its domain membership and graph
edges remain explicit K antecedents. This is not row collection, a product
matrix, or a PA proof translation. -/
namespace PASoundness.PAtoCompactMultiplicationNewRowSuffixOrder
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactSuccCongruenceOrderAlpha
open PASoundness.PAtoCompactZeroSuccessor
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def suffixOrder : Formula := replace 1 40 (replace 0 31 orderFormula)

private def MF1 : Formula := replace 30 4 M5
private def MF2 : Formula := replace 31 8 MF1
private def MF3 : Formula := replace 32 5 MF2
private def MF4 : Formula := replace 33 9 MF3
private def PF : Formula := .imp orderFormula MF4

private def point_F : KDerivation PF.encode := by
  let F1 : Formula := .all 31 (.all 32 (.all 33 M5))
  have h1 := universalInstance 30 4 F1 (by decide) (by decide) (by decide)
  have e1 : replace 30 4 F1 = .all 31 (.all 32 (.all 33 MF1)) := by decide
  rw [e1] at h1
  let F2 : Formula := .all 32 (.all 33 MF1)
  have h2 := universalInstance 31 8 F2 (by decide) (by decide) (by decide)
  have e2 : replace 31 8 F2 = .all 32 (.all 33 MF2) := by decide
  rw [e2] at h2
  let F3 : Formula := .all 33 MF2
  have h3 := universalInstance 32 5 F3 (by decide) (by decide) (by decide)
  have e3 : replace 32 5 F3 = .all 33 MF3 := by decide
  rw [e3] at h3
  have h4 := universalInstance 33 9 MF3 (by decide) (by decide) (by decide)
  have e4 : replace 33 9 MF3 = MF4 := rfl
  rw [e4] at h4
  have hc : KDerivation (imp orderFormula.encode MF4.encode) := by
    exact compose order_alpha (compose h1 (compose h2 (compose h3 h4)))
  exact hc

/-- The actual suffix order clause implies its forward point instance,
including both source guards, both target guards and both graph edges. -/
def forward_instance : KDerivation (imp suffixOrder.encode
    (imp (both (member 31 4) (both (member 31 8)
      (both (member 40 5) (both (member 40 9)
        (both (graphFormula 6 4 5).encode (graphFormula 6 8 9).encode)))))
      (both (imp (member 8 4) (member 9 5))
        (imp (member 9 5) (member 8 4))))) := by
  have h31 := universalInstance 0 31 PF (by decide) (by decide) (by decide)
  have hp31 : KDerivation (replace 0 31 PF).encode := .mp (.generalize 0 point_F) h31
  have h40 := universalInstance 1 40 (replace 0 31 PF) (by decide) (by decide) (by decide)
  have hp40 : KDerivation (replace 1 40 (replace 0 31 PF)).encode := .mp (.generalize 1 hp31) h40
  have hs : replace 1 40 (replace 0 31 PF) =
      .imp suffixOrder (.imp (namedBoth (.member 31 4) (namedBoth (.member 31 8)
        (namedBoth (.member 40 5) (namedBoth (.member 40 9)
          (namedBoth (graphFormula 6 4 5) (graphFormula 6 8 9))))))
        (namedBoth (.imp (.member 8 4) (.member 9 5))
          (.imp (.member 9 5) (.member 8 4)))) := by decide
  rw [hs] at hp40
  simpa [Formula.encode, namedBoth, Formula.not, CompactProof.both, neg] using hp40

private def MR1 : Formula := replace 30 8 M5
private def MR2 : Formula := replace 31 4 MR1
private def MR3 : Formula := replace 32 9 MR2
private def MR4 : Formula := replace 33 5 MR3
private def PR : Formula := .imp orderFormula MR4

private def point_R : KDerivation PR.encode := by
  let F1 : Formula := .all 31 (.all 32 (.all 33 M5))
  have h1 := universalInstance 30 8 F1 (by decide) (by decide) (by decide)
  have e1 : replace 30 8 F1 = .all 31 (.all 32 (.all 33 MR1)) := by decide
  rw [e1] at h1
  let F2 : Formula := .all 32 (.all 33 MR1)
  have h2 := universalInstance 31 4 F2 (by decide) (by decide) (by decide)
  have e2 : replace 31 4 F2 = .all 32 (.all 33 MR2) := by decide
  rw [e2] at h2
  let F3 : Formula := .all 33 MR2
  have h3 := universalInstance 32 9 F3 (by decide) (by decide) (by decide)
  have e3 : replace 32 9 F3 = .all 33 MR3 := by decide
  rw [e3] at h3
  have h4 := universalInstance 33 5 MR3 (by decide) (by decide) (by decide)
  have e4 : replace 33 5 MR3 = MR4 := rfl
  rw [e4] at h4
  have hc : KDerivation (imp orderFormula.encode MR4.encode) := by
    exact compose order_alpha (compose h1 (compose h2 (compose h3 h4)))
  exact hc

/-- The actual suffix order clause implies its reverse point instance,
including both source guards, both target guards and both graph edges. -/
def reverse_instance : KDerivation (imp suffixOrder.encode
    (imp (both (member 31 8) (both (member 31 4)
      (both (member 40 9) (both (member 40 5)
        (both (graphFormula 6 8 9).encode (graphFormula 6 4 5).encode)))))
      (both (imp (member 4 8) (member 5 9))
        (imp (member 5 9) (member 4 8))))) := by
  have h31 := universalInstance 0 31 PR (by decide) (by decide) (by decide)
  have hp31 : KDerivation (replace 0 31 PR).encode := .mp (.generalize 0 point_R) h31
  have h40 := universalInstance 1 40 (replace 0 31 PR) (by decide) (by decide) (by decide)
  have hp40 : KDerivation (replace 1 40 (replace 0 31 PR)).encode := .mp (.generalize 1 hp31) h40
  have hs : replace 1 40 (replace 0 31 PR) =
      .imp suffixOrder (.imp (namedBoth (.member 31 8) (namedBoth (.member 31 4)
        (namedBoth (.member 40 9) (namedBoth (.member 40 5)
          (namedBoth (graphFormula 6 8 9) (graphFormula 6 4 5))))))
        (namedBoth (.imp (.member 4 8) (.member 5 9))
          (.imp (.member 5 9) (.member 4 8)))) := by decide
  rw [hs] at hp40
  simpa [Formula.encode, namedBoth, Formula.not, CompactProof.both, neg] using hp40

theorem forward_instance_certificate : theoremCode (certificate forward_instance) =
    imp suffixOrder.encode
      (imp (both (member 31 4) (both (member 31 8)
        (both (member 40 5) (both (member 40 9)
          (both (graphFormula 6 4 5).encode (graphFormula 6 8 9).encode)))))
        (both (imp (member 8 4) (member 9 5))
          (imp (member 9 5) (member 8 4)))) := certificate_correct _

theorem reverse_instance_certificate : theoremCode (certificate reverse_instance) =
    imp suffixOrder.encode
      (imp (both (member 31 8) (both (member 31 4)
        (both (member 40 9) (both (member 40 5)
          (both (graphFormula 6 8 9).encode (graphFormula 6 4 5).encode)))))
        (both (imp (member 4 8) (member 5 9))
          (imp (member 5 9) (member 4 8)))) := certificate_correct _

end PASoundness.PAtoCompactMultiplicationNewRowSuffixOrder
#print axioms PASoundness.PAtoCompactMultiplicationNewRowSuffixOrder.forward_instance
#print axioms PASoundness.PAtoCompactMultiplicationNewRowSuffixOrder.reverse_instance
#print axioms PASoundness.PAtoCompactMultiplicationNewRowSuffixOrder.forward_instance_certificate
#print axioms PASoundness.PAtoCompactMultiplicationNewRowSuffixOrder.reverse_instance_certificate
