import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.CompactQuantifiers

/-! Capture-safe instances and K vacuity for the restricted reverse graph
correspondence. The family is definitionally the globalBackward premise in
PAtoCompactRestrictedInverseClause. It is an explicit hypothesis, not a
construction of a graph. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactOrderIsoRestrictedGlobal
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def conj (a b : Formula) : Formula := (a.imp b.not).not

def restrictedBody : Formula := .imp (conj (.member 1 3) (.member 0 4))
  (.imp (graphFormula 7 3 4) (graphFormula 6 4 3))
def restrictedFamily : Formula := .all 3 (.all 4 restrictedBody)
def atFirst : Formula := .imp (conj (.member 1 3) (.member 0 2))
  (.imp (graphFormula 7 3 2) (graphFormula 6 2 3))
def atSecond : Formula := .imp (conj (.member 1 5) (.member 0 4))
  (.imp (graphFormula 7 5 4) (graphFormula 6 4 5))

/-- The supplied restricted family yields both fixed guarded edge conversions. -/
def restricted_instances : KDerivation
    (imp restrictedFamily.encode (both atFirst.encode atSecond.encode)) := by
  have hi₃ := allSpecialize 3 (.all 4 restrictedBody) (by decide)
  have hi₄ := universalInstance 4 2 restrictedBody (by decide) (by decide) (by decide)
  have first : KDerivation (imp restrictedFamily.encode atFirst.encode) := by
    have h : KDerivation (imp (allCode 4 restrictedBody.encode) atFirst.encode) := by
      have he : replace 4 2 restrictedBody = atFirst := by decide
      rw [he] at hi₄
      exact hi₄
    exact compose hi₃ h
  have hj₃ := universalInstance 3 5 (.all 4 restrictedBody) (by decide) (by decide) (by decide)
  have second : KDerivation (imp restrictedFamily.encode atSecond.encode) := by
    have h : KDerivation (imp restrictedFamily.encode (allCode 4 atSecond.encode)) := by
      have he : replace 3 5 (.all 4 restrictedBody) = .all 4 atSecond := by decide
      rw [he] at hj₃
      exact hj₃
    exact compose h (allSpecialize 4 atSecond (by decide))
  apply Context.closeEmpty
  apply Context.deduction
  have hr : Context [restrictedFamily.encode] restrictedFamily.encode := Context.head [] _
  exact Context.conjunctionIntro (.mp hr (.closed first)) (.mp hr (.closed second))

theorem restricted_instances_certificate : theoremCode (certificate restricted_instances) =
    imp restrictedFamily.encode (both atFirst.encode atSecond.encode) :=
  certificate_correct restricted_instances

private theorem family_names_lt : ∀ v ∈ restrictedFamily.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ restrictedFamily.names.sup id at hm
  have hb : restrictedFamily.names.sup id < 30 := by decide
  omega

def freshFamily := freshen restrictedFamily 30 family_names_lt

/-- Freshen bound names before deriving vacuity, retaining finite K proofs. -/
def family_vacuity (v : Nat) (fresh : v ∉ freshFamily.formula.names) :
    KDerivation (imp restrictedFamily.encode (allCode v restrictedFamily.encode)) :=
  compose freshFamily.equivalent.forward (compose (freshFamily.formula.vacuity v fresh)
    (allCongr v freshFamily.equivalent.backward))

theorem fresh_2 : 2 ∉ freshFamily.formula.names := by decide
theorem fresh_3 : 3 ∉ freshFamily.formula.names := by decide
theorem fresh_4 : 4 ∉ freshFamily.formula.names := by decide
theorem fresh_5 : 5 ∉ freshFamily.formula.names := by decide

end PASoundness.PAtoCompactOrderIsoRestrictedGlobal

#print axioms PASoundness.PAtoCompactOrderIsoRestrictedGlobal.restricted_instances
#print axioms PASoundness.PAtoCompactOrderIsoRestrictedGlobal.family_vacuity
