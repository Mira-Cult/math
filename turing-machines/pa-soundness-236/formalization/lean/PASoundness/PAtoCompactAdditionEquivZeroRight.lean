import PASoundness.PAtoCompactEquivalentZero
import PASoundness.PAtoCompactOrdinalAddition

/-! If the left object of the literal addition equivalence is empty, the
right object is empty too. This is a K derivation using the second bijection
clause, with no candidate-domain premise or semantic assumption. Negation
is literally implication to code 1. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionEquivZeroRight
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactEmptyExtrema
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrdinalAddition
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def secondBody : Formula := match bijectionFormula with
 | .imp (.imp _ (.imp (.all _ f) _)) _ => f
 | _ => .bottom
private def witnessBody : Formula := match secondBody with
 | .imp _ (.ex _ f) => f
 | _ => .bottom
private def matrix : Formula := (bijectionFormula.imp orderFormula.not).not

private def witness_false : KDerivation (imp (zeroCode 0 7)
    (allCode 2 (imp witnessBody.encode 1))) := by
  let Z := zeroCode 0 7
  apply Context.closeEmpty
  apply Context.deduction
  have hh : Context [Z] (imp witnessBody.encode 1) := by
    apply Context.deduction
    have hw : Context [witnessBody.encode,Z] witnessBody.encode := Context.head _ _
    have hm : Context [witnessBody.encode,Z] (member 0 2) := by
      change Context [witnessBody.encode,Z] (both (member 0 2) _) at hw
      exact Context.conjunctionLeft hw
    have hz : Context [witnessBody.encode,Z] Z := .hypothesis (by simp)
    have hn := Context.mp hz (.closed (zero_excludes 0 7 2 (by decide) (by decide)))
    exact .mp hm hn
  have hv : ∀ h, h ∈ [Z] → KDerivation (imp h (allCode 2 h)) := by
    intro h hh
    have he : h=Z := by simpa using hh
    subst h
    exact zero_vacuity 0 7 2 (by decide) (by decide)
  exact Context.generalize 2 hv hh

private def matrix_false : KDerivation (imp (zeroCode 0 7)
    (imp (member 1 3) (imp matrix.encode 1))) := by
  let Z := zeroCode 0 7
  let M := member 1 3
  let A := matrix.encode
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [A,M,Z]
  have ha : Context Γ A := Context.head _ _
  have hm : Context Γ M := .hypothesis (by simp [Γ])
  have hz : Context Γ Z := .hypothesis (by simp [Γ])
  have hb : Context Γ bijectionFormula.encode := Context.conjunctionLeft ha
  have hf : Context Γ (allCode 3 secondBody.encode) := Context.conjunctionRight hb
  have hs : Context Γ secondBody.encode := .mp hf (.closed (allSpecialize 3 secondBody (by decide)))
  have he : Context Γ (existsCode 2 witnessBody.encode) := .mp hm hs
  have hi : Context Γ (allCode 2 (imp witnessBody.encode 1)) := .mp hz (.closed witness_false)
  exact Context.existsElim (explosion (allCode 2 1)) hi he

private def zeroLeft_excludes_equiv_of_member : KDerivation (imp (zeroCode 0 7)
    (imp (member 1 3) (neg equivalentFormula.encode))) := by
  let Z := zeroCode 0 7
  let M := member 1 3
  let E := equivalentFormula.encode
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [E,M,Z]
  have he : Context Γ (existsCode 6 matrix.encode) := Context.head _ _
  have hlocal : Context [M,Z] (imp matrix.encode 1) :=
    .mp (Context.head [Z] M) (.mp (Context.head [] Z |> fun h => Context.under h M) (.closed matrix_false))
  have hv : ∀ h, h ∈ [M,Z] → KDerivation (imp h (allCode 6 h)) := by
    intro h hh
    by_cases hM : h = M
    · subst h
      exact (show KDerivation (imp (member 1 3) (allCode 6 (member 1 3))) from
        Formula.vacuity 6 (.member 1 3) (by decide))
    · have hZ : h = Z := by simpa [hM] using hh
      subst h
      exact zero_vacuity 0 7 6 (by decide) (by decide)
  have hall : Context [M,Z] (allCode 6 (imp matrix.encode 1)) := Context.generalize 6 hv hlocal
  exact Context.existsElim (explosion (allCode 6 1)) (Context.under hall E) he

private theorem equiv_names_lt : ∀ v ∈ equivalentFormula.names, v < 30 := by
  intro v hv
  have h := Finset.le_sup (f := id) hv
  change v ≤ equivalentFormula.names.sup id at h
  have hb : equivalentFormula.names.sup id < 30 := by decide
  omega
private def freshEquiv := freshen equivalentFormula 30 equiv_names_lt
private def equivalent_vacuity3 : KDerivation
    (imp equivalentFormula.encode (allCode 3 equivalentFormula.encode)) := by
  have hf : 3 ∉ freshEquiv.formula.names := by decide
  exact compose freshEquiv.equivalent.forward
    (compose (freshEquiv.formula.vacuity 3 hf)
      (allCongr 3 freshEquiv.equivalent.backward))

private def equivalent_zero_left : KDerivation
    (imp (zeroCode 0 7) (imp equivalentFormula.encode (zeroCode 1 3))) := by
  let Z := zeroCode 0 7
  let E := equivalentFormula.encode
  let Γ := [E,Z]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  have hlocal : Context Γ (neg (member 1 3)) := by
    apply Context.deduction
    let Δ := [member 1 3,E,Z]
    have hm : Context Δ (member 1 3) := Context.head _ _
    have he : Context Δ E := .hypothesis (by simp [Δ])
    have hz : Context Δ Z := .hypothesis (by simp [Δ])
    have hn : Context Δ (neg E) :=
      .mp hm (.mp hz (.closed zeroLeft_excludes_equiv_of_member))
    exact .mp he hn
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 3 h)) := by
    intro h hh
    by_cases he : h = E
    · subst h
      exact equivalent_vacuity3
    · have hz : h = Z := by simpa [Γ, he] using hh
      subst h
      exact zero_vacuity 0 7 3 (by decide) (by decide)
  exact Context.generalize 3 hv hlocal

private def zero0 : Formula := .all 36 (Formula.member 0 36).not
private def zero1 : Formula := .all 37 (Formula.member 1 37).not
private def source : Formula := zero0.imp (equivalentFormula.imp zero1)
private def moved : Formula := replace 0 31 source
private def zero0_alpha : KDerivation (imp (zeroCode 0 36) (zeroCode 0 7)) := by
  have h := universalAlpha 36 7 ((Formula.member 0 36).not) (by decide) (by decide) (by decide)
  simpa [zeroCode, Formula.not, Formula.encode, replace, rename, neg] using h.1
private def zero1_alpha : KDerivation (imp (zeroCode 1 3) (zeroCode 1 37)) := by
  have h := universalAlpha 3 37 ((Formula.member 1 3).not) (by decide) (by decide) (by decide)
  simpa [zeroCode, Formula.not, Formula.encode, replace, rename, neg] using h.1
private def source_proved : KDerivation source.encode := by
  let Z := zeroCode 0 36
  let E := equivalentFormula.encode
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [E,Z]
  have he : Context Γ E := Context.head _ _
  have hz : Context Γ Z := .hypothesis (by simp [Γ])
  have hz' : Context Γ (zeroCode 0 7) := .mp hz (.closed zero0_alpha)
  have ho : Context Γ (zeroCode 1 3) := .mp he (.mp hz' (.closed equivalent_zero_left))
  exact .mp ho (.closed zero1_alpha)
private def moved_proved : KDerivation moved.encode := by
  have hi := universalInstance 0 31 source (by decide) (by decide) (by decide)
  exact .mp (.generalize 0 source_proved) hi

/-- K derives the zero graph of the right operand from the zero left operand
and the literal equivalence used by the addition formula. -/
def addition_equiv_zero_right : KDerivation (imp (zeroCode 31 36)
    (imp (equivAt 31 34).encode (zeroCode 34 37))) := by
  have hi := universalInstance 1 34 moved (by decide) (by decide) (by decide)
  have h := KDerivation.mp (.generalize 1 moved_proved) hi
  simpa [moved, source, zero0, zero1, equivAt, replace, rename, Formula.encode,
    Formula.not, zeroCode, neg] using h

theorem addition_equiv_zero_right_certificate :
    theoremCode (certificate addition_equiv_zero_right) = imp (zeroCode 31 36)
      (imp (equivAt 31 34).encode (zeroCode 34 37)) :=
  certificate_correct addition_equiv_zero_right
end PASoundness.PAtoCompactAdditionEquivZeroRight
#print axioms PASoundness.PAtoCompactAdditionEquivZeroRight.addition_equiv_zero_right
#print axioms PASoundness.PAtoCompactAdditionEquivZeroRight.addition_equiv_zero_right_certificate
