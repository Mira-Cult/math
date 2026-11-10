import PASoundness.PAtoCompactProductCleanRetain

/-! Transfer of the fixed selected-output uniqueness clause through a
product-graph filter. The reverse triple-edge implication remains an
explicit K proof input. This is not product-matrix preservation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductCleanForwardUnique
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactProductCleanFilter
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Triple edge at fixed source names 3,4 and competing output 9. -/
def triple9 (g : Nat) : Formula := .ex 18
  (namedBoth (pairFormula 18 3 4) (graphFormula g 18 9))

/-- For selected output 5, every represented competing output 9 equals 5. -/
def unique5 (g : Nat) : Formula := .all 9
  (.imp (namedBoth (.member 2 9) (triple9 g)) (.equal 9 5))

private def filterNamed : Formula := .all 55 (namedFilterBody 6 54 55 (cleanPredicate 55))
private theorem filter_named_code : filterNamed.encode = filterCode 54 := by rfl
private def point (g : Nat) : Formula :=
  .imp (namedBoth (.member 2 9) (triple9 g)) (.equal 9 5)

/-- The filter is vacuous at the quantified competitor label. -/
def filter_vacuity9 : KDerivation (imp (filterCode 54) (allCode 9 (filterCode 54))) := by
  have h := filterNamed.vacuity 9 (by decide)
  simpa only [filter_named_code] using h

/-- Given literal K proof data that the filtered competing triple is also an
old triple, transfer old uniqueness to the filtered graph. The reverse-triple
input is explicit; no graph existence or semantics is assumed. -/
def unique_transfer
    (reverseTriple : KDerivation (imp (filterCode 54)
      (imp (triple9 54).encode (triple9 6).encode))) :
    KDerivation (imp (filterCode 54) (imp (unique5 6).encode (unique5 54).encode)) := by
  have hpoint : KDerivation (imp (filterCode 54)
      (imp (point 6).encode (point 54).encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let F := filterCode 54
    let A := both (member 2 9) (triple9 54).encode
    let Γ := [A,(point 6).encode,F]
    have ha : Context Γ A := .head _ _
    have ho : Context Γ (point 6).encode := .hypothesis (by simp [Γ])
    have hf : Context Γ F := .hypothesis (by simp [Γ])
    have hmem : Context Γ (member 2 9) := Context.conjunctionLeft ha
    have hnew : Context Γ (triple9 54).encode := Context.conjunctionRight ha
    have hold : Context Γ (triple9 6).encode := .mp hnew (.mp hf (.closed reverseTriple))
    have heq : Context Γ (equal 9 5) := .mp (Context.conjunctionIntro hmem hold) ho
    exact heq
  simpa only [unique5, Formula.encode, point] using
    conditionalAllCongr 9 filter_vacuity9 hpoint

theorem unique_transfer_certificate
    (reverseTriple : KDerivation (imp (filterCode 54)
      (imp (triple9 54).encode (triple9 6).encode))) :
    theoremCode (certificate (unique_transfer reverseTriple)) =
      imp (filterCode 54) (imp (unique5 6).encode (unique5 54).encode) :=
  certificate_correct (unique_transfer reverseTriple)
end PASoundness.PAtoCompactProductCleanForwardUnique
#print axioms PASoundness.PAtoCompactProductCleanForwardUnique.filter_vacuity9
#print axioms PASoundness.PAtoCompactProductCleanForwardUnique.unique_transfer
#print axioms PASoundness.PAtoCompactProductCleanForwardUnique.unique_transfer_certificate
