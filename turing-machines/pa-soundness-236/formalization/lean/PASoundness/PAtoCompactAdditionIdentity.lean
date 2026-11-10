import PASoundness.PAtoCompactAdditionEmptySuffix
import PASoundness.PAtoCompactAdditionSuffixClosed
import PASoundness.CompactQuantifiers
import PASoundness.PAtoCompactAdditionTwoZeros

/-! K constructs the proposed addition formula from an explicitly equal cut,
a zero right operand, and the given E relation to the cut. The proof constructs
the suffix in K and uses a concrete K isomorphism between two zero objects.
It does not prove arithmetic totality, quotient congruence, or PA soundness.
Negation is the literal compact implication to code 1. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionIdentity
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactAdditionEmptySuffix PASoundness.PAtoCompactAdditionSuffixClosed
attribute [local irreducible] imp Cantor.pair Cantor.triangle
private def andF (a b : Formula) : Formula := (a.imp b.not).not
private def orF (a b : Formula) : Formula := a.not.imp b
private def E : Formula := .equal 32 33
private def Z : Formula := .all 36 (Formula.member 31 36).not
private def H : Formula := equivAt 30 33
private def F : Formula := suffixFormula
private def B : Formula := andF (orF (.equal 33 32) (.member 32 33))
  (andF H (andF F (equivAt 31 34)))
private def A : Formula := andF E (andF Z H)

private theorem formula_eq : additionFormula = .ex 33 (.ex 34 B) := by rfl
private theorem formula_suffix : F.encode =
    PASoundness.PAtoCompactFilteredSubset.filterGraph 32 34 35 (neg (member 33 35)) := by rfl
private theorem formula_zero : Z.encode = zeroCode 31 36 := by rfl
private theorem A_fresh : 34 ∉ A.names := by decide
private theorem B_binders : 33 ∉ (Formula.ex 34 B).binders := by decide

private def identity_witness :
    KDerivation (imp A.encode additionFormula.encode) := by
  have hs : KDerivation (imp A.encode (imp F.encode B.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [F.encode,A.encode]
    have hf : Context Γ F.encode := .head _ _
    have ha : Context Γ A.encode := .hypothesis (by simp [Γ])
    have he : Context Γ E.encode := Context.conjunctionLeft ha
    have hz0 : Context Γ Z.encode := Context.conjunctionLeft (Context.conjunctionRight ha)
    have hh : Context Γ H.encode := Context.conjunctionRight (Context.conjunctionRight ha)
    have hzero : Context Γ (zeroCode 34 37) := by
      have hp := equal_cut_empty_suffix 32 33 34 35 37 (by decide)
      apply Context.mp (by simpa [formula_suffix] using hf)
      exact Context.mp (by simpa [E,Formula.encode] using he) (.closed hp)
    have heq : Context Γ (equivAt 31 34).encode :=
      .mp hzero (.mp (by simpa [formula_zero] using hz0) (.closed PASoundness.PAtoCompactAdditionTwoZeros.two_zeros_equivalent_addition))
    have heq' : Context Γ (equal 33 32) :=
      .mp (by simpa [E,Formula.encode] using he) (.closed (equalitySymmetry 32 33))
    have hor : Context Γ (either (equal 33 32) (member 32 33)) := Context.disjunctionLeft heq'
    change Context Γ (both (either (equal 33 32) (member 32 33))
      (both H.encode (both F.encode (equivAt 31 34).encode)))
    exact Context.conjunctionIntro hor (Context.conjunctionIntro hh (Context.conjunctionIntro hf heq))
  have hv := A.vacuity 34 A_fresh
  have hcong := conditionalExistsCongr 34 hv hs
  apply Context.closeEmpty
  apply Context.deduction
  have ha : Context [A.encode] A.encode := .head _ _
  have he : Context [A.encode] (existsCode 34 B.encode) :=
    .mp (.closed suffix_exists) (.mp ha (.closed hcong))
  have hi := existsIntroduce 33 (.ex 34 B) B_binders
  have hresult := Context.mp he (.closed hi)
  simpa [formula_eq,Formula.encode] using hresult
/-- Given an equal cut, a zero right summand, and E of the left summand to
that cut, K constructs the exact proposed addition relation. The hypotheses
are explicit and no candidate-domain or quotient laws are inferred. -/
def addition_of_equal_cut : KDerivation (imp (equal 32 33)
    (imp (zeroCode 31 36) (imp (equivAt 30 33).encode additionFormula.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(equivAt 30 33).encode,zeroCode 31 36,equal 32 33]
  have he : Context Γ E.encode := by
    simpa [E,Formula.encode] using (Context.hypothesis (Γ := Γ) (a := equal 32 33) (by simp [Γ]))
  have hz : Context Γ Z.encode := by
    simpa [formula_zero] using (Context.hypothesis (Γ := Γ) (a := zeroCode 31 36) (by simp [Γ]))
  have hh : Context Γ H.encode := .head _ _
  have ha : Context Γ A.encode := Context.conjunctionIntro he (Context.conjunctionIntro hz hh)
  exact .mp ha (.closed identity_witness)

theorem addition_of_equal_cut_certificate :
    theoremCode (certificate addition_of_equal_cut) = imp (equal 32 33)
      (imp (zeroCode 31 36) (imp (equivAt 30 33).encode additionFormula.encode)) :=
  certificate_correct addition_of_equal_cut

end PASoundness.PAtoCompactAdditionIdentity
#print axioms PASoundness.PAtoCompactAdditionIdentity.addition_of_equal_cut
#print axioms PASoundness.PAtoCompactAdditionIdentity.addition_of_equal_cut_certificate
