import PASoundness.PAtoCompactGraphMeaning
import PASoundness.PAtoCompactIsomorphismRigidity

/-! Standard-HF rigidity of the concrete order-isomorphism formula on finite
ordinal codes. This is a semantic property, not a K quotient or proof
translation. -/
namespace PASoundness.PAtoCompactIsomorphismRigidityClosed
open PASoundness.CompactNamed PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactGraphMeaning PASoundness.PAtoCompactIsomorphismRigidity
open PASoundness.CompactMatrix (Environment)
open PASoundness.HFCoding

/-- The proposed graph-isomorphism formula can relate finite standard
ordinals only when their natural indices agree. -/
theorem ordinal_rigidity (ρ : Environment) (n m : Nat)
    (h0 : ρ 0 = (ordinal n).code) (h1 : ρ 1 = (ordinal m).code)
    (hE : equivalentFormula.Realize ρ) : n = m := by
  exact PAtoCompactIsomorphismRigidity.ordinal_rigidity ρ n m graphRel h0 h1
    (fun η => graphFormula_realize_iff 6 2 3 η (by decide) (by decide) (by decide))
    (fun η => graphFormula_realize_iff 6 2 4 η (by decide) (by decide) (by decide))
    (fun η => graphFormula_realize_iff 6 4 3 η (by decide) (by decide) (by decide)) hE

end PASoundness.PAtoCompactIsomorphismRigidityClosed

#print axioms PASoundness.PAtoCompactIsomorphismRigidityClosed.ordinal_rigidity
