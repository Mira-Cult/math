import PASoundness.PAtoCompactQuotientSuccNeZero

/-! A universally quantified K successor-not-zero schema under a retained
zero-graph parameter. This is an object-level proof, not a full reverse PA
interpretation or a semantic soundness argument. Compact code 1 is unchanged. -/

set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccNeZeroSchema
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactEmptyExtrema
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactQuotientSuccNeZero
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- For any input and successor output, that output cannot be related by the
candidate equivalence to the retained zero object. The zero graph uses its
original bound name 7, and its vacuity at both quantified names is proved. -/
def successor_not_zero_schema : KDerivation
    (imp (zeroCode 1 7) (allCode 2 (allCode 0
      (imp (successorCode 2 0 3) (neg equivalentFormula.encode))))) := by
  let Z := zeroCode 1 7
  let S := successorCode 2 0 3
  let N := neg equivalentFormula.encode
  apply Context.closeEmpty
  apply Context.deduction
  have hlocal : Context [Z] (imp S N) := by
    apply Context.deduction
    have hs : Context [S,Z] S := Context.head _ _
    have hz : Context [S,Z] Z := .hypothesis (by simp)
    exact .mp hz (.mp hs (.closed successor_not_equivalent_zero))
  have hv0 : ∀ h, h ∈ [Z] → KDerivation (imp h (allCode 0 h)) := by
    intro h hh
    have he : h = Z := by simpa using hh
    subst h
    exact zero_vacuity 1 7 0 (by decide) (by decide)
  have hv2 : ∀ h, h ∈ [Z] → KDerivation (imp h (allCode 2 h)) := by
    intro h hh
    have he : h = Z := by simpa using hh
    subst h
    exact zero_vacuity 1 7 2 (by decide) (by decide)
  exact Context.generalize 2 hv2 (Context.generalize 0 hv0 hlocal)

theorem successor_not_zero_schema_certificate :
    theoremCode (certificate successor_not_zero_schema) =
      imp (zeroCode 1 7) (allCode 2 (allCode 0
        (imp (successorCode 2 0 3) (neg equivalentFormula.encode)))) :=
  certificate_correct successor_not_zero_schema

end PASoundness.PAtoCompactSuccNeZeroSchema

#print axioms PASoundness.PAtoCompactSuccNeZeroSchema.successor_not_zero_schema
#print axioms PASoundness.PAtoCompactSuccNeZeroSchema.successor_not_zero_schema_certificate
