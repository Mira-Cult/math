import PASoundness.PAtoCompactPartialCompositionBase
import PASoundness.CompactQuantifiers
import PASoundness.CompactFreshen

/-! Exact K pointwise instantiation and freshening-based vacuity for the
partial-composition invariant. These are syntactic proof constructors; they
do not construct a composition graph, prove successor preservation, or
establish quotient transitivity. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialCompositionInstantiate
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPartialCompositionBase
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Exact pointwise matrix, keeping graph and middle witnesses within the
unchanged named partial-composition formula. -/
def pointFormula : Formula := match partialComposition with
  | .all _ (.all _ f) => f
  | _ => .truth

/-- The original quantified invariant implies its literal instance at names
2 and 3, without changing either graph-edge orientation. -/
def partial_composition_instance : KDerivation
    (imp partialComposition.encode pointFormula.encode) := by
  have h₂ := allSpecialize 2 (.all 3 pointFormula) (by decide)
  have h₃ := allSpecialize 3 pointFormula (by decide)
  exact compose h₂ h₃

theorem partial_composition_instance_certificate :
    theoremCode (certificate partial_composition_instance) =
      imp partialComposition.encode pointFormula.encode :=
  certificate_correct partial_composition_instance

/-- Expanded pointwise interface with the shared existential middle witness. -/
theorem point_formula_code : pointFormula.encode =
    imp (both (member 0 2) (member 8 3))
      (both (imp (graphFormula 9 2 3).encode
        (both (member 10 2)
          (existsCode 4 (both (member 1 4)
            (both (graphFormula 6 2 4).encode (graphFormula 7 4 3).encode)))))
        (imp (both (member 10 2)
          (existsCode 4 (both (member 1 4)
            (both (graphFormula 6 2 4).encode (graphFormula 7 4 3).encode))))
          (graphFormula 9 2 3).encode)) := by rfl

private theorem names_lt : ∀ v ∈ partialComposition.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ partialComposition.names.sup id at hm
  have hb : partialComposition.names.sup id < 30 := by decide
  omega

def freshPartial := freshen partialComposition 30 names_lt

theorem fresh_partial_2 : 2 ∉ freshPartial.formula.names := by decide
theorem fresh_partial_3 : 3 ∉ freshPartial.formula.names := by decide

/-- The queried names occur as binders, so first alpha-freshen the entire
invariant before constructing literal K vacuity. -/
def partial_composition_vacuity (v : Nat) (fresh : v ∉ freshPartial.formula.names) :
    KDerivation (imp partialComposition.encode (allCode v partialComposition.encode)) :=
  compose freshPartial.equivalent.forward
    (compose (freshPartial.formula.vacuity v fresh)
      (allCongr v freshPartial.equivalent.backward))

def partial_composition_vacuity_2 :
    KDerivation (imp partialComposition.encode (allCode 2 partialComposition.encode)) :=
  partial_composition_vacuity 2 fresh_partial_2

def partial_composition_vacuity_3 :
    KDerivation (imp partialComposition.encode (allCode 3 partialComposition.encode)) :=
  partial_composition_vacuity 3 fresh_partial_3

theorem partial_composition_vacuity_2_certificate :
    theoremCode (certificate partial_composition_vacuity_2) =
      imp partialComposition.encode (allCode 2 partialComposition.encode) :=
  certificate_correct partial_composition_vacuity_2

theorem partial_composition_vacuity_3_certificate :
    theoremCode (certificate partial_composition_vacuity_3) =
      imp partialComposition.encode (allCode 3 partialComposition.encode) :=
  certificate_correct partial_composition_vacuity_3

end PASoundness.PAtoCompactPartialCompositionInstantiate

#print axioms PASoundness.PAtoCompactPartialCompositionInstantiate.partial_composition_instance
#print axioms PASoundness.PAtoCompactPartialCompositionInstantiate.partial_composition_vacuity_2
#print axioms PASoundness.PAtoCompactPartialCompositionInstantiate.partial_composition_vacuity_3
