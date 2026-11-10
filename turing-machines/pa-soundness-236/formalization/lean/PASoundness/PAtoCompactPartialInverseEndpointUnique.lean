import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.CompactDerivations

/-! One pointwise consequence of supplied old-graph functionality for the
partial-inverse successor endpoint. The uniqueness clause, membership, source
equality, and old edge are explicit antecedents; they are not established here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseEndpointUnique
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def conj (a b : Formula) : Formula := (a.imp b.not).not

def uniqueBody : Formula := .imp
  (conj (.member 1 4) (graphFormula 6 12 4)) (.equal 4 13)
def suppliedUniqueness : Nat := allCode 4 uniqueBody.encode

/-- The uniqueness clause at endpoint 12 and designated image 13 forces an
arbitrary old-graph image 3 to equal 13, provided 3 belongs to domain 1 and
its source 2 equals endpoint 12. -/
def endpoint_image_unique : KDerivation
    (imp suppliedUniqueness (imp (member 1 3) (imp (equal 12 2)
      (imp (graphFormula 6 2 3).encode (equal 13 3))))) := by
  have hi := universalInstance 4 3 uniqueBody (by decide) (by decide) (by decide)
  have hinst : replace 4 3 uniqueBody = .imp
      (conj (.member 1 3) (graphFormula 6 12 3)) (.equal 3 13) := by decide
  rw [hinst] at hi
  have hrepl := (equalityReplace 2 12 (graphFormula 6 2 3) (by decide) (by decide)).1
  have hsyntax : replace 2 12 (graphFormula 6 2 3) = graphFormula 6 12 3 := by decide
  rw [hsyntax] at hrepl
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 6 2 3).encode,equal 12 2,member 1 3,suppliedUniqueness]
  have hg : Context Γ (graphFormula 6 2 3).encode := Context.head _ _
  have he : Context Γ (equal 12 2) := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 1 3) := .hypothesis (by simp [Γ])
  have hu : Context Γ suppliedUniqueness := .hypothesis (by simp [Γ])
  have hg' : Context Γ (graphFormula 6 12 3).encode :=
    .mp hg (.mp (Context.eqSymm he) (.closed hrepl))
  have hc : Context Γ (imp (both (member 1 3) (graphFormula 6 12 3).encode)
      (equal 3 13)) := .mp hu (.closed hi)
  exact Context.eqSymm (.mp (Context.conjunctionIntro hm hg') hc)

theorem endpoint_image_unique_certificate :
    theoremCode (certificate endpoint_image_unique) =
      imp suppliedUniqueness (imp (member 1 3) (imp (equal 12 2)
        (imp (graphFormula 6 2 3).encode (equal 13 3)))) :=
  certificate_correct endpoint_image_unique

end PASoundness.PAtoCompactPartialInverseEndpointUnique

#print axioms PASoundness.PAtoCompactPartialInverseEndpointUnique.endpoint_image_unique
#print axioms PASoundness.PAtoCompactPartialInverseEndpointUnique.endpoint_image_unique_certificate
