import PASoundness.PAtoCompactAdditionIdentity

/-! Eliminating the auxiliary cut from the right-zero construction.
The original addition formula, including its existential cut binder, is
retained literally. No arithmetic totality or quotient axiom is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionIdentityClosedCut
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactAdditionIdentity
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private def body : Formula := match additionFormula with
  | .ex _ p => p
  | _ => .bottom

private def freshAddition : Formula := .ex 38 (replace 33 38 body)

/-- The actual K proof that the literal addition formula is vacuous at its
bound cut name. This uses alpha-conversion, not a syntactic freshness claim
about the original formula. -/
def addition_cut_vacuity : KDerivation
    (imp additionFormula.encode (allCode 33 additionFormula.encode)) := by
  have hα := existentialAlpha 33 38 body (by decide) (by decide) (by decide)
  have hf : 33 ∉ freshAddition.names := by
    simp only [freshAddition, Formula.names, Finset.mem_insert, not_or]
    exact ⟨by decide, replace_avoids 33 38 body (by decide) (by decide)⟩
  have hv := freshAddition.vacuity 33 hf
  have hforward : KDerivation (imp additionFormula.encode freshAddition.encode) := by
    simpa only [additionFormula, body, freshAddition, Formula.encode] using hα.1
  have hback : KDerivation (imp freshAddition.encode additionFormula.encode) := by
    simpa only [additionFormula, body, freshAddition, Formula.encode] using hα.2
  exact compose hforward (compose hv (allCongr 33 hback))

/-- K constructs the proposed addition formula when the right summand is
zero and the first summand is isomorphic to the result. The auxiliary cut is
chosen equal to the result and eliminated inside K. -/
def addition_of_zero_right : KDerivation
    (imp (zeroCode 31 36) (imp (equivAt 30 32).encode additionFormula.encode)) := by
  let Z := zeroCode 31 36
  let H := (equivAt 30 32).encode
  let A := additionFormula.encode
  let E := equal 33 32
  have hreplace : replace 32 33 (equivAt 30 32) = equivAt 30 33 := by decide
  have htransport : KDerivation
      (imp (equal 32 33) (imp H (equivAt 30 33).encode)) := by
    have h := (equalityReplace 32 33 (equivAt 30 32) (by decide) (by decide)).1
    simpa only [hreplace] using h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [H,Z]
  have hlocal : Context Γ (imp E A) := by
    apply Context.deduction
    have he : Context (E :: Γ) E := Context.head _ _
    have hz : Context (E :: Γ) Z := Context.under (Context.under (Context.head [] Z) H) E
    have hh : Context (E :: Γ) H := Context.under (Context.head [Z] H) E
    have he' : Context (E :: Γ) (equal 32 33) :=
      .mp he (.closed (equalitySymmetry 33 32))
    have hequiv : Context (E :: Γ) (equivAt 30 33).encode :=
      .mp hh (.mp he' (.closed htransport))
    exact .mp hequiv (.mp hz (.mp he' (.closed addition_of_equal_cut)))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 33 h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases he : h = H
    · subst h
      exact (equivAt 30 32).vacuity 33 (by decide)
    · have he' : h = Z := hh.resolve_left he
      subst h
      exact PAtoCompactEmptyExtrema.zero_vacuity 31 36 33 (by decide) (by decide)
  have hall : Context Γ (allCode 33 (imp E A)) := Context.generalize 33 hv hlocal
  exact Context.existsElim addition_cut_vacuity hall (.closed (existsEqual 33 32))

theorem addition_of_zero_right_certificate :
    theoremCode (certificate addition_of_zero_right) =
      imp (zeroCode 31 36) (imp (equivAt 30 32).encode additionFormula.encode) :=
  certificate_correct addition_of_zero_right

end PASoundness.PAtoCompactAdditionIdentityClosedCut

#print axioms PASoundness.PAtoCompactAdditionIdentityClosedCut.addition_cut_vacuity
#print axioms PASoundness.PAtoCompactAdditionIdentityClosedCut.addition_of_zero_right
#print axioms PASoundness.PAtoCompactAdditionIdentityClosedCut.addition_of_zero_right_certificate
