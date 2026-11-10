import PASoundness.PAtoCompactAdditionZeroSuffixContained
import PASoundness.PAtoCompactAdditionEquivZeroRight
import PASoundness.PAtoCompactAdditionSuffixAlignment

/-! Literal K converse for addition by a represented zero. This is one
arithmetic-relation fact, not a proof of addition totality, quotient
congruence, or PA soundness. Code 1 remains literal self-membership. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionRightZeroConverse
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactEmptyExtrema
open PASoundness.PAtoCompactOrdinalAddition PASoundness.PAtoCompactAdditionSuffixAlignment
open PASoundness.PAtoCompactAdditionZeroSuffixContained PASoundness.PAtoCompactAdditionEquivZeroRight
attribute [local irreducible] imp Cantor.pair Cantor.triangle
private def andF (a b : Formula) : Formula := (a.imp b.not).not
private def orF (a b : Formula) : Formula := a.not.imp b
private def B : Formula := andF (orF (.equal 33 32) (.member 32 33))
  (andF (equivAt 30 33) (andF suffixFormula (equivAt 31 34)))
private def T : Formula := equivAt 30 32
private def Z : Nat := zeroCode 31 36
private theorem add_eq : additionFormula = .ex 33 (.ex 34 B) := by rfl
private theorem suffix_eq : suffixFormula.encode =
    PASoundness.PAtoCompactFilteredSubset.filterGraph 32 34 35 (neg (member 33 35)) := by rfl
private theorem T_fresh33 : 33 ∉ T.names := by decide
private theorem T_fresh34 : 34 ∉ T.names := by decide

private def zero_alpha : KDerivation (imp (zeroCode 34 37) (zeroCode 34 36)) := by
  have h := universalAlpha 37 36 ((Formula.member 34 37).not) (by decide) (by decide) (by decide)
  simpa [zeroCode, Formula.not, Formula.encode, replace, rename, neg] using h.1

private def equiv_subst : KDerivation (imp (equal 33 32)
    (imp (equivAt 30 33).encode T.encode)) := by
  have h := (equalityReplace 33 32 (equivAt 30 33) (by decide) (by decide)).1
  have hs : replace 33 32 (equivAt 30 33) = equivAt 30 32 := by decide
  rw [hs] at h
  exact h

private def point : KDerivation (imp Z (imp B.encode T.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [B.encode,Z]
  have hb : Context Γ B.encode := .head _ _
  have hz : Context Γ Z := .hypothesis (by simp [Γ])
  change Context Γ (both (either (equal 33 32) (member 32 33))
    (both (equivAt 30 33).encode (both suffixFormula.encode (equivAt 31 34).encode))) at hb
  have ha := Context.conjunctionLeft hb
  have hrest := Context.conjunctionRight hb
  have he := Context.conjunctionLeft hrest
  have hs := Context.conjunctionLeft (Context.conjunctionRight hrest)
  have hezero := Context.conjunctionRight (Context.conjunctionRight hrest)
  have hz37 : Context Γ (zeroCode 34 37) :=
    .mp hezero (.mp hz (.closed addition_equiv_zero_right))
  have hz36 : Context Γ (zeroCode 34 36) := .mp hz37 (.closed zero_alpha)
  have hcut := zero_suffix_cut_equal
  change KDerivation (imp (zeroCode 34 36)
    (imp (PASoundness.PAtoCompactFilteredSubset.filterGraph 32 34 35 (neg (member 33 35)))
      (imp (either (equal 33 32) (member 32 33)) (equal 33 32)))) at hcut
  have hequal : Context Γ (equal 33 32) :=
    .mp ha (.mp (by simpa [suffix_eq] using hs) (.mp hz36 (.closed hcut)))
  exact .mp he (.mp hequal (.closed equiv_subst))

/-- If the right summand has the displayed zero graph, the proposed addition
relation implies equivalence of its left summand and result. -/
def addition_zero_right_converse : KDerivation
    (imp (zeroCode 31 36) (imp additionFormula.encode (equivAt 30 32).encode)) := by
  let X := existsCode 34 B.encode
  let Γ := [Z]
  have hz : Context Γ Z := .head _ _
  have hv34 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 34 h)) := by
    intro h hh
    have hz' : h = Z := by simpa [Γ] using hh
    subst h
    exact zero_vacuity 31 36 34 (by decide) (by decide)
  have hv33 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 33 h)) := by
    intro h hh
    have hz' : h = Z := by simpa [Γ] using hh
    subst h
    exact zero_vacuity 31 36 33 (by decide) (by decide)
  have hall34 : Context Γ (allCode 34 (imp B.encode T.encode)) :=
    Context.generalize 34 hv34 (.mp hz (.closed point))
  have hinner : Context Γ (imp X T.encode) := by
    apply Context.deduction
    exact Context.existsElim (T.vacuity 34 T_fresh34) (.under hall34 _) (.head _ _)
  have hall33 : Context Γ (allCode 33 (imp X T.encode)) :=
    Context.generalize 33 hv33 hinner
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  have hresult : Context [additionFormula.encode,Z] T.encode := by
    apply Context.existsElim (T.vacuity 33 T_fresh33) (.under hall33 _)
    simpa [add_eq,Formula.encode,X] using (Context.head [Z] additionFormula.encode)
  exact hresult

theorem addition_zero_right_converse_certificate :
    theoremCode (certificate addition_zero_right_converse) =
      imp (zeroCode 31 36) (imp additionFormula.encode (equivAt 30 32).encode) :=
  certificate_correct addition_zero_right_converse
end PASoundness.PAtoCompactAdditionRightZeroConverse
#print axioms PASoundness.PAtoCompactAdditionRightZeroConverse.addition_zero_right_converse
#print axioms PASoundness.PAtoCompactAdditionRightZeroConverse.addition_zero_right_converse_certificate
