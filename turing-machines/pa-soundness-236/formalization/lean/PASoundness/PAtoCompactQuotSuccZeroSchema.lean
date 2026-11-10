import PASoundness.PAtoCompactQuotSuccNotEquivalentZero

/-! A quantified K form of the literal quotient-successor separation result.
The displayed zero graph remains an object-level premise. This module does not
assert an existential zero witness or a complete PA-to-K interpretation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactQuotSuccZeroSchema
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactEmptyExtrema
open PASoundness.PAtoCompactQuotientSuccessor
open PASoundness.PAtoCompactConditionalTransitivityWitnessInterface
open PASoundness.PAtoCompactQuotSuccNotEquivalentZero
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- With a fixed zero object at name 8, every literal quotient successor at
names 0 and 1 is distinct from it under the displayed E(1,8) relation.
The successor formula retains its own candidate-domain and witness guards. -/
def quotient_successor_not_zero_schema : KDerivation
    (imp (zeroCode 8 7) (allCode 0 (allCode 1
      (imp successorFormula.encode (neg secondEquivalent.encode))))) := by
  let Z := zeroCode 8 7
  let S := successorFormula.encode
  let N := neg secondEquivalent.encode
  apply Context.closeEmpty
  apply Context.deduction
  have hlocal : Context [Z] (imp S N) := by
    apply Context.deduction
    have hs : Context [S,Z] S := Context.head _ _
    have hz : Context [S,Z] Z := Context.under (Context.head [] Z) S
    exact .mp hz (.mp hs (.closed quotient_successor_not_equivalent_zero))
  have hv1 : ∀ h, h ∈ [Z] → KDerivation (imp h (allCode 1 h)) := by
    intro h hh
    have he : h = Z := by simpa using hh
    subst h
    exact zero_vacuity 8 7 1 (by decide) (by decide)
  have hv0 : ∀ h, h ∈ [Z] → KDerivation (imp h (allCode 0 h)) := by
    intro h hh
    have he : h = Z := by simpa using hh
    subst h
    exact zero_vacuity 8 7 0 (by decide) (by decide)
  exact Context.generalize 0 hv0 (Context.generalize 1 hv1 hlocal)

/-- Universal closure over the displayed zero object. Its zero-graph guard
remains inside the outer quantifier. -/
def quotient_successor_not_zero_schema_all : KDerivation
    (allCode 8 (imp (zeroCode 8 7) (allCode 0 (allCode 1
      (imp successorFormula.encode (neg secondEquivalent.encode)))))) :=
  .generalize 8 quotient_successor_not_zero_schema

theorem quotient_successor_not_zero_schema_certificate :
    theoremCode (certificate quotient_successor_not_zero_schema) =
      imp (zeroCode 8 7) (allCode 0 (allCode 1
        (imp successorFormula.encode (neg secondEquivalent.encode)))) :=
  certificate_correct quotient_successor_not_zero_schema

theorem quotient_successor_not_zero_schema_all_certificate :
    theoremCode (certificate quotient_successor_not_zero_schema_all) =
      allCode 8 (imp (zeroCode 8 7) (allCode 0 (allCode 1
        (imp successorFormula.encode (neg secondEquivalent.encode))))) :=
  certificate_correct quotient_successor_not_zero_schema_all

end PASoundness.PAtoCompactQuotSuccZeroSchema

#print axioms PASoundness.PAtoCompactQuotSuccZeroSchema.quotient_successor_not_zero_schema
#print axioms PASoundness.PAtoCompactQuotSuccZeroSchema.quotient_successor_not_zero_schema_all
#print axioms PASoundness.PAtoCompactQuotSuccZeroSchema.quotient_successor_not_zero_schema_certificate
#print axioms PASoundness.PAtoCompactQuotSuccZeroSchema.quotient_successor_not_zero_schema_all_certificate
