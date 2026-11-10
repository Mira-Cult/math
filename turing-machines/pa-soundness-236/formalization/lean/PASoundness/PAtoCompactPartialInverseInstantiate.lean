import PASoundness.PAtoCompactPartialInverseBase
import PASoundness.CompactQuantifiers
import PASoundness.CompactFreshen

/-! Pointwise K instantiation and freshening-based vacuity for the exact
partial-inverse invariant. These are syntactic proof constructors; neither
an inverse graph nor successor preservation is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseInstantiate
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPartialInverseBase
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Exact matrix of the quantified partial inverse. -/
def pointFormula : Formula := match partialInverse with
  | .all _ (.all _ f) => f
  | _ => .truth

/-- The original invariant implies its literal instance at names 2 and 3. -/
def partial_inverse_instance : KDerivation (imp partialInverse.encode pointFormula.encode) := by
  have h₂ := allSpecialize 2 (.all 3 pointFormula) (by decide)
  have h₃ := allSpecialize 3 pointFormula (by decide)
  exact compose h₂ h₃

theorem partial_inverse_instance_certificate :
    theoremCode (certificate partial_inverse_instance) =
      imp partialInverse.encode pointFormula.encode :=
  certificate_correct partial_inverse_instance

/-- Fully expanded pointwise interface: 2 and 3 range over the input domains,
then the inverse edge and prefix-limited original edge are equivalent. -/
theorem point_formula_code : pointFormula.encode =
    imp (both (member 0 2) (member 1 3))
      (both (imp (graphFormula 7 3 2).encode
        (both (member 8 2) (graphFormula 6 2 3).encode))
        (imp (both (member 8 2) (graphFormula 6 2 3).encode)
          (graphFormula 7 3 2).encode)) := by rfl

private theorem names_lt : ∀ v ∈ partialInverse.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ partialInverse.names.sup id at hm
  have hb : partialInverse.names.sup id < 30 := by decide
  omega

def freshPartial := freshen partialInverse 30 names_lt

theorem fresh_partial_2 : 2 ∉ freshPartial.formula.names := by decide
theorem fresh_partial_3 : 3 ∉ freshPartial.formula.names := by decide

/-- Names 2 and 3 are bound in the original invariant, so direct syntactic
absence is unavailable. Alpha-freshening provides the required K vacuity. -/
def partial_inverse_vacuity (v : Nat) (fresh : v ∉ freshPartial.formula.names) :
    KDerivation (imp partialInverse.encode (allCode v partialInverse.encode)) :=
  compose freshPartial.equivalent.forward
    (compose (freshPartial.formula.vacuity v fresh)
      (allCongr v freshPartial.equivalent.backward))

def partial_inverse_vacuity_2 :
    KDerivation (imp partialInverse.encode (allCode 2 partialInverse.encode)) :=
  partial_inverse_vacuity 2 fresh_partial_2

def partial_inverse_vacuity_3 :
    KDerivation (imp partialInverse.encode (allCode 3 partialInverse.encode)) :=
  partial_inverse_vacuity 3 fresh_partial_3

theorem partial_inverse_vacuity_2_certificate :
    theoremCode (certificate partial_inverse_vacuity_2) =
      imp partialInverse.encode (allCode 2 partialInverse.encode) :=
  certificate_correct partial_inverse_vacuity_2

theorem partial_inverse_vacuity_3_certificate :
    theoremCode (certificate partial_inverse_vacuity_3) =
      imp partialInverse.encode (allCode 3 partialInverse.encode) :=
  certificate_correct partial_inverse_vacuity_3

end PASoundness.PAtoCompactPartialInverseInstantiate

#print axioms PASoundness.PAtoCompactPartialInverseInstantiate.partial_inverse_instance
#print axioms PASoundness.PAtoCompactPartialInverseInstantiate.partial_inverse_vacuity_2
#print axioms PASoundness.PAtoCompactPartialInverseInstantiate.partial_inverse_vacuity_3
