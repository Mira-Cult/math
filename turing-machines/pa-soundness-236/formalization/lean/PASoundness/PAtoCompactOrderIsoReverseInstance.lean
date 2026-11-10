import PASoundness.PAtoCompactOrderIsoInstance
import PASoundness.PAtoCompactIsoInverseGuard

/-! Composition of the actual candidate order-clause instantiation with a
pointwise inverse-edge condition. It does not quantify the inverse relation,
construct an inverse graph, or establish symmetry. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactOrderIsoReverseInstance
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrderIsoInstance
open PASoundness.PAtoCompactIsoInverseGuard
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def firstInverseEdge : Nat := imp (graphFormula 7 3 2).encode (graphFormula 6 2 3).encode
def secondInverseEdge : Nat := imp (graphFormula 7 5 4).encode (graphFormula 6 4 5).encode

def reverseMatrix : Nat :=
  imp (both (member 1 3) (both (member 1 5) (both (member 0 2)
    (both (member 0 4) (both (graphFormula 7 3 2).encode (graphFormula 7 5 4).encode)))))
    (both (imp (member 5 3) (member 4 2)) (imp (member 4 2) (member 5 3)))

/-- The candidate's exact forward order clause and the two displayed local
inverse-edge implications entail its reversed guarded order instance. -/
def reverse_order_instance : KDerivation
    (imp firstInverseEdge (imp secondInverseEdge (imp orderFormula.encode reverseMatrix))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [orderFormula.encode,secondInverseEdge,firstInverseEdge]
  have ho : Context Γ orderFormula.encode := Context.head _ _
  have hi₁ : Context Γ firstInverseEdge := .hypothesis (by simp [Γ])
  have hi₂ : Context Γ secondInverseEdge := .hypothesis (by simp [Γ])
  have hm : Context Γ orderMatrix.encode := .mp ho (.closed order_instance)
  have hc : Context Γ (imp firstInverseEdge
      (imp secondInverseEdge (imp orderMatrix.encode reverseMatrix))) :=
    .closed (reverse_guarded (member 0 2) (member 0 4) (member 1 3) (member 1 5)
      (graphFormula 6 2 3).encode (graphFormula 6 4 5).encode
      (graphFormula 7 3 2).encode (graphFormula 7 5 4).encode
      (member 4 2) (member 5 3))
  exact .mp hm (.mp hi₂ (.mp hi₁ hc))

theorem reverse_order_instance_certificate :
    theoremCode (certificate reverse_order_instance) =
      imp firstInverseEdge (imp secondInverseEdge (imp orderFormula.encode reverseMatrix)) :=
  certificate_correct reverse_order_instance

end PASoundness.PAtoCompactOrderIsoReverseInstance

#print axioms PASoundness.PAtoCompactOrderIsoReverseInstance.reverse_order_instance
#print axioms PASoundness.PAtoCompactOrderIsoReverseInstance.reverse_order_instance_certificate
