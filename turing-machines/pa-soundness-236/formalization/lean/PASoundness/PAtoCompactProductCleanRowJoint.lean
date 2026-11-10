import PASoundness.PAtoCompactProductCleanRebased303132
import PASoundness.PAtoCompactCleanSuffixRowDomainAnyBase
import PASoundness.PAtoCompactFreeNames
import PASoundness.PAtoCompactFreeVacuity

/-! Jointly construct the SAME cleaned old product graph, clean suffix graph,
and full-prefix row graph. The old product relation and suffix equivalence
remain literal antecedents. This does not prove the new product matrix,
multiplication totality or PA interpretation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductCleanRowJoint
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactProductCleanRebased303132
open PASoundness.PAtoCompactCleanSuffixRow64 PASoundness.PAtoCompactCleanSuffixRowDomainAnyBase
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFreeVacuity
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The actual old graph is shared with the nested clean suffix and row
witnesses. The row graph has been alpha-rebound to 64 for lex point 7. -/
def jointResult : Formula := .ex 10 (namedBoth (namedBoth oldMatrixActual oldCleanActual) result64)

def conditions (base : Nat) : Formula :=
  namedBoth (domainAt base 31) (PAtoCompactOrdinalAddition.equivAt 31 40)

private theorem conditions_free10 (base : Nat) : 10 ∉ (conditions base).free := by
  intro h
  have hh : 10 ∈ (domainAt base 31).free ∨
      10 ∈ (PAtoCompactOrdinalAddition.equivAt 31 40).free := by
    simpa [conditions,namedBoth,Formula.not,Formula.free] using h
  rcases hh with hd | he
  · have hd' := domainAt_free base 31 hd
    simp at hd'
  · have he' : 10 ∉ (PAtoCompactOrdinalAddition.equivAt 31 40).free := by decide
    exact he' he

/-- From an actual old product and a candidate index equivalent to the suffix,
K constructs the old clean graph, clean map and associated row graph in one
nested witness package. Name 10 is one shared old graph, and 6 one shared map. -/
noncomputable def product_with_clean_suffix_and_row (base : Nat) : KDerivation
    (imp oldProduct.encode (imp (conditions base).encode jointResult.encode)) := by
  let oldBody := namedBoth oldMatrixActual oldCleanActual
  have hpoint : KDerivation (imp (conditions base).encode (imp oldBody.encode
      (namedBoth oldBody result64).encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [oldBody.encode,(conditions base).encode]
    have ho : Context Γ oldBody.encode := .head _ _
    have ha : Context Γ (both (domainAt base 31).encode
        (PAtoCompactOrdinalAddition.equivAt 31 40).encode) := by
      have hh : Context Γ (conditions base).encode := .hypothesis (by simp [Γ])
      simpa [conditions,namedBoth,Formula.not,Formula.encode,both,neg] using hh
    have hr : Context Γ result64.encode :=
      .mp (Context.conjunctionRight ha) (.mp (Context.conjunctionLeft ha)
        (.closed (clean_suffix_with_row_domain base)))
    simpa [namedBoth,Formula.not,Formula.encode,both,neg] using Context.conjunctionIntro ho hr
  have hlift := conditionalExistsCongr 10 (free_vacuity 10 (conditions base)
    (conditions_free10 base)) hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(conditions base).encode,oldProduct.encode]
  have ha : Context Γ (conditions base).encode := .head _ _
  have hp : Context Γ oldProduct.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ (existsCode 10 oldBody.encode) := by
    simpa [oldBody] using (Context.mp hp (.closed clean_old_product_at_names))
  have hr := Context.mp hg (Context.mp ha (.closed hlift))
  simpa [jointResult,oldBody,Formula.encode] using hr

theorem product_with_clean_suffix_and_row_certificate (base : Nat) :
    theoremCode (certificate (product_with_clean_suffix_and_row base)) =
      imp oldProduct.encode (imp (conditions base).encode jointResult.encode) :=
  certificate_correct _
end PASoundness.PAtoCompactProductCleanRowJoint
#print axioms PASoundness.PAtoCompactProductCleanRowJoint.product_with_clean_suffix_and_row
#print axioms PASoundness.PAtoCompactProductCleanRowJoint.product_with_clean_suffix_and_row_certificate
