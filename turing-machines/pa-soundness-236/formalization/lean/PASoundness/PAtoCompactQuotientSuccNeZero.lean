import PASoundness.PAtoCompactOrderIsoZero

/-! An object-level K proof that the fixed successor and zero graph outputs
are not related by the candidate quotient equivalence. The contradiction uses
the literal first bijection clause and the literal compact bottom code `1`.
This proves neither quotient congruence nor a reverse PA proof translation. -/

set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactQuotientSuccNeZero
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactEmptyExtrema
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrderIsoZero
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def firstBody : Formula := match bijectionFormula with
 | .imp (.imp (.all _ f) _) _ => f
 | _ => .bottom

private def witnessBody : Formula := match firstBody with
 | .imp _ (.ex _ f) => f
 | _ => .bottom

private def matrix : Formula := (bijectionFormula.imp orderFormula.not).not

private def witness_false : KDerivation (imp (zeroCode 1 7)
    (allCode 3 (imp witnessBody.encode 1))) := by
  let Z := zeroCode 1 7
  apply Context.closeEmpty
  apply Context.deduction
  have hh : Context [Z] (imp witnessBody.encode 1) := by
    apply Context.deduction
    have hw : Context [witnessBody.encode,Z] witnessBody.encode := Context.head _ _
    have hm : Context [witnessBody.encode,Z] (member 1 3) := by
      change Context [witnessBody.encode,Z] (both (member 1 3) _) at hw
      exact Context.conjunctionLeft hw
    have hz : Context [witnessBody.encode,Z] Z := .hypothesis (by simp)
    have hn := Context.mp hz (.closed (zero_excludes 1 7 3 (by decide) (by decide)))
    exact .mp hm hn
  have hv : ∀ h, h ∈ [Z] → KDerivation (imp h (allCode 3 h)) := by
    intro h hh
    have he : h=Z := by simpa using hh
    subst h
    exact zero_vacuity 1 7 3 (by decide) (by decide)
  exact Context.generalize 3 hv hh

private def matrix_false : KDerivation (imp (zeroCode 1 7)
    (imp (member 0 2) (imp matrix.encode 1))) := by
  let Z := zeroCode 1 7
  let M := member 0 2
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
  have hb' : Context Γ (both (allCode 2 firstBody.encode) (allCode 3 (imp (member 1 3) rightConsequent))) := by exact hb
  have hf : Context Γ (allCode 2 firstBody.encode) := Context.conjunctionLeft hb' 
  have hs : Context Γ firstBody.encode := .mp hf (.closed (allSpecialize 2 firstBody (by decide)))
  have he : Context Γ (existsCode 3 witnessBody.encode) := .mp hm hs
  have hi : Context Γ (allCode 3 (imp witnessBody.encode 1)) := .mp hz (.closed witness_false)
  exact Context.existsElim (explosion (allCode 3 1)) hi he

def zeroRight_excludes_equiv_of_member : KDerivation (imp (zeroCode 1 7)
    (imp (member 0 2) (neg equivalentFormula.encode))) := by
  let Z := zeroCode 1 7
  let M := member 0 2
  let E := equivalentFormula.encode
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [E,M,Z]
  have hz : Context Γ Z := .hypothesis (by simp [Γ])
  have hm : Context Γ M := .hypothesis (by simp [Γ])
  have he : Context Γ (existsCode 6 matrix.encode) := Context.head _ _
  have hlocal : Context [M,Z] (imp matrix.encode 1) :=
    .mp (Context.head [Z] M) (.mp (Context.head [] Z |> fun h => Context.under h M) (.closed matrix_false))
  have hv : ∀ h, h ∈ [M,Z] → KDerivation (imp h (allCode 6 h)) := by
    intro h hh
    by_cases hM : h = M
    · subst h
      exact (show KDerivation (imp (member 0 2) (allCode 6 (member 0 2))) from
        Formula.vacuity 6 (.member 0 2) (by decide))
    · have hZ : h = Z := by simpa [hM] using hh
      subst h
      exact zero_vacuity 1 7 6 (by decide) (by decide)
  have hall : Context [M,Z] (allCode 6 (imp matrix.encode 1)) := Context.generalize 6 hv hlocal
  exact Context.existsElim (explosion (allCode 6 1)) (Context.under hall E) he

/-- The successor graph contains its input. If its output were related by the
candidate equivalence to a zero-graph output, the first bijection clause would
produce a member of that zero object. -/
def successor_not_equivalent_zero : KDerivation
    (imp (successorCode 2 0 3)
      (imp (zeroCode 1 7) (neg equivalentFormula.encode))) := by
  let S := successorCode 2 0 3
  let Z := zeroCode 1 7
  let Γ := [Z,S]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  have hz : Context Γ Z := Context.head _ _
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 0 2) :=
    .mp hs (.closed (successor_contains_input 2 0 3 (by decide) (by decide)))
  exact .mp hm (.mp hz (.closed zeroRight_excludes_equiv_of_member))

theorem successor_not_equivalent_zero_certificate :
    theoremCode (certificate successor_not_equivalent_zero) =
      imp (successorCode 2 0 3)
        (imp (zeroCode 1 7) (neg equivalentFormula.encode)) :=
  certificate_correct successor_not_equivalent_zero

end PASoundness.PAtoCompactQuotientSuccNeZero

#print axioms PASoundness.PAtoCompactQuotientSuccNeZero.zeroRight_excludes_equiv_of_member
#print axioms PASoundness.PAtoCompactQuotientSuccNeZero.successor_not_equivalent_zero
#print axioms PASoundness.PAtoCompactQuotientSuccNeZero.successor_not_equivalent_zero_certificate
