import PASoundness.PAtoCompactPartialInverseEndpointUnique
import PASoundness.PAtoCompactPartialInverseImageWitness

/-! Pointwise functionality extracted from one supplied actual image witness.
The image remains an existential witness in the caller; no choice, prefix
alias, inverse graph or full successor invariant is introduced here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseImageFunction
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactPartialInverseEndpointUnique
open PASoundness.PAtoCompactPartialInverseImageWitness
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- With a supplied actual image witness for endpoint 12, any target-domain
edge from equal source 2 has the same target 13. -/
def image_witness_functional : KDerivation
    (imp imageWitness (imp (member 1 3) (imp (equal 12 2)
      (imp (graphFormula 6 2 3).encode (equal 13 3))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [imageWitness]
  have hw : Context Γ imageWitness := Context.head [] _
  have hu : Context Γ suppliedUniqueness :=
    Context.conjunctionRight (Context.conjunctionRight hw)
  exact .mp hu (.closed endpoint_image_unique)

theorem image_witness_functional_certificate :
    theoremCode (certificate image_witness_functional) =
      imp imageWitness (imp (member 1 3) (imp (equal 12 2)
        (imp (graphFormula 6 2 3).encode (equal 13 3)))) :=
  certificate_correct image_witness_functional

end PASoundness.PAtoCompactPartialInverseImageFunction

#print axioms PASoundness.PAtoCompactPartialInverseImageFunction.image_witness_functional
#print axioms PASoundness.PAtoCompactPartialInverseImageFunction.image_witness_functional_certificate
