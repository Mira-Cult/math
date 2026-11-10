import PASoundness.PAtoCompactAdditionRightZeroSchemaAllocated
import PASoundness.PAtoCompactAdditionRightZeroSchemaFixed
import PASoundness.PAtoCompactCandidateDynamicReflexivity

/-! A same-output right-zero addition relation, constructed as finite K proof
    data. The two labels may coincide; the bounds are syntactic allocator bounds. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PASoundness.PAtoCompactPAAddZeroRelation
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation

/-- A candidate added to a zero has the candidate itself as an addition output. -/
def right_zero_same_output (b a z : Nat) (ha : a < b+2) (hz : z < b+2) :
    KDerivation (imp (domainAt b a).encode
      (imp (zeroAt b z).encode (addAt b a z a).encode)) := by
  have he := PASoundness.PAtoCompactCandidateDynamicReflexivity.dynamic_reflexive b a ha
  have hschema := PASoundness.PAtoCompactAdditionRightZeroSchemaAllocated.schema_of_fixed
    true b a z a ha hz ha PASoundness.PAtoCompactAdditionRightZeroSchemaFixed.fixed_backward
  change KDerivation (imp (zeroAt b z).encode
    (imp (equivAt b a a).encode (addAt b a z a).encode)) at hschema
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(zeroAt b z).encode, (domainAt b a).encode]
  have hz' : Context Γ (zeroAt b z).encode := .head _ _
  have ha' : Context Γ (domainAt b a).encode := .hypothesis (by simp [Γ])
  exact .mp (.mp ha' (.closed he)) (.mp hz' (.closed hschema))

theorem right_zero_same_output_certificate (b a z : Nat) (ha : a < b+2) (hz : z < b+2) :
    theoremCode (certificate (right_zero_same_output b a z ha hz)) =
      imp (domainAt b a).encode (imp (zeroAt b z).encode (addAt b a z a).encode) :=
  certificate_correct _

end PASoundness.PAtoCompactPAAddZeroRelation

#print axioms PASoundness.PAtoCompactPAAddZeroRelation.right_zero_same_output
#print axioms PASoundness.PAtoCompactPAAddZeroRelation.right_zero_same_output_certificate
