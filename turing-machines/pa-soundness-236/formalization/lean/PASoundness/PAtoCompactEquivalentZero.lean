import PASoundness.PAtoCompactQuotientSuccNeZero
import PASoundness.CompactFreshen

/-! An object equivalent to a zero object has no members. This is an
object-level K derivation for the displayed fixed labels; no semantic model
argument or general quotient interpretation is assumed. -/

set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactEquivalentZero
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactEmptyExtrema
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactQuotientSuccNeZero
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private theorem equiv_names_lt : ∀ v ∈ equivalentFormula.names, v < 30 := by
  intro v hv
  have h := Finset.le_sup (f := id) hv
  change v ≤ equivalentFormula.names.sup id at h
  have hb : equivalentFormula.names.sup id < 30 := by decide
  omega

private def freshEquiv := freshen equivalentFormula 30 equiv_names_lt

/-- The free name 2 is absent from E, but occurs as a bound name in its
literal syntax. Its vacuity is established by a K alpha-freshening proof. -/
def equivalent_vacuity2 : KDerivation
    (imp equivalentFormula.encode (allCode 2 equivalentFormula.encode)) := by
  have hf : 2 ∉ freshEquiv.formula.names := by decide
  exact compose freshEquiv.equivalent.forward
    (compose (freshEquiv.formula.vacuity 2 hf)
      (allCongr 2 freshEquiv.equivalent.backward))

/-- A zero object on the right of the proposed isomorphism forces the object
on the left to satisfy the literal zero graph at fresh binder 8. -/
def equivalent_zero : KDerivation
    (imp (zeroCode 1 7) (imp equivalentFormula.encode (zeroCode 0 8))) := by
  let Z := zeroCode 1 7
  let E := equivalentFormula.encode
  let Γ := [E,Z]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  have hlocal : Context Γ (neg (member 0 2)) := by
    apply Context.deduction
    let Δ := [member 0 2,E,Z]
    have hm : Context Δ (member 0 2) := Context.head _ _
    have he : Context Δ E := .hypothesis (by simp [Δ])
    have hz : Context Δ Z := .hypothesis (by simp [Δ])
    have hn : Context Δ (neg E) :=
      .mp hm (.mp hz (.closed zeroRight_excludes_equiv_of_member))
    exact .mp he hn
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 2 h)) := by
    intro h hh
    by_cases he : h = E
    · subst h
      exact equivalent_vacuity2
    · have hz : h = Z := by simpa [Γ, he] using hh
      subst h
      exact zero_vacuity 1 7 2 (by decide) (by decide)
  have hzero : Context Γ (zeroCode 0 2) := by
    exact Context.generalize 2 hv hlocal
  have ha : KDerivation (imp (zeroCode 0 2) (zeroCode 0 8)) := by
    have h := universalAlpha 2 8 ((.member 0 2 : Formula).not)
      (by decide) (by decide) (by decide)
    simpa [zeroCode, Formula.not, Formula.encode, replace, rename, neg] using h.1
  exact .mp hzero (.closed ha)

theorem equivalent_zero_certificate : theoremCode (certificate equivalent_zero) =
    imp (zeroCode 1 7) (imp equivalentFormula.encode (zeroCode 0 8)) :=
  certificate_correct equivalent_zero

end PASoundness.PAtoCompactEquivalentZero

#print axioms PASoundness.PAtoCompactEquivalentZero.equivalent_vacuity2
#print axioms PASoundness.PAtoCompactEquivalentZero.equivalent_zero
#print axioms PASoundness.PAtoCompactEquivalentZero.equivalent_zero_certificate
