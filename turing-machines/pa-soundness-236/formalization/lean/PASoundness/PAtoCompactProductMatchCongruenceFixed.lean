import PASoundness.PAtoCompactProductMatchInputWitnesses
import PASoundness.PAtoCompactProductMatchCollectionConditional
import PASoundness.PAtoCompactSuccGraphOutputLift
import PASoundness.PAtoCompactFreeVacuity

/-! Fixed-label guarded product congruence from two product formulas and
two factor-equivalence formulas. Matrix graph witnesses are eliminated by
finite K existential rules; the source candidate remains explicit. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchCongruenceFixed

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductMatchTargetOutput
open PASoundness.PAtoCompactProductMatchFactorImages PASoundness.PAtoCompactProductMatchFactorOrderPoint
open PASoundness.PAtoCompactProductMatchCollectionInsideConditional PASoundness.PAtoCompactProductMatchCollectionConditional
open PASoundness.PAtoCompactProductMatchCollectionOrderUnique PASoundness.PAtoCompactProductMatchInputWitnesses
open PASoundness.PAtoCompactProductMatchEquivFixed PASoundness.PAtoCompactSuccGraphOutputLift PASoundness.PAtoCompactFreeVacuity

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def baseGuard : Formula := namedBoth (candidateFormula 2)
  (namedBoth targetProduct (namedBoth firstEquivalent secondEquivalent))
def guard1 : Formula := namedBoth baseGuard productMatrix
def guard2 : Formula := namedBoth guard1 targetMatrix
def guard3 : Formula := namedBoth guard2 firstMatrix
def result : Formula := equivAt 100 2 44

def matrix_point : KDerivation (imp guard3.encode (imp secondMatrix.encode result.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [secondMatrix.encode,guard3.encode]
  have hs : Context Γ secondMatrix.encode := .head _ _
  have hg : Context Γ guard3.encode := .hypothesis (by simp [Γ])
  have hg' : Context Γ (both guard2.encode firstMatrix.encode) := by
    simpa [guard3, namedBoth, Formula.not, Formula.encode, both, neg] using hg
  have h2 : Context Γ (both guard1.encode targetMatrix.encode) := by
    simpa [guard2, namedBoth, Formula.not, Formula.encode, both, neg] using Context.conjunctionLeft hg'
  have h1 : Context Γ (both baseGuard.encode productMatrix.encode) := by
    simpa [guard1, namedBoth, Formula.not, Formula.encode, both, neg] using Context.conjunctionLeft h2
  have h0 : Context Γ (both (candidateFormula 2).encode
      (both targetProduct.encode (both firstEquivalent.encode secondEquivalent.encode))) := by
    simpa [baseGuard, namedBoth, Formula.not, Formula.encode, both, neg] using Context.conjunctionLeft h1
  have hf₁ : Context Γ (both firstBijection.encode firstOrder.encode) := by
    simpa [firstMatrix, namedBoth, Formula.not, Formula.encode, both, neg] using Context.conjunctionRight hg'
  have hf₂ : Context Γ (both secondBijection.encode secondOrder.encode) := by
    simpa [secondMatrix, namedBoth, Formula.not, Formula.encode, both, neg] using hs
  have hmat : Context Γ extendedMatrices.encode := by
    have h := Context.conjunctionIntro
      (Context.conjunctionIntro (Context.conjunctionRight h1)
        (Context.conjunctionIntro (Context.conjunctionLeft hf₁)
          (Context.conjunctionIntro (Context.conjunctionLeft hf₂) (Context.conjunctionRight h2))))
      (Context.conjunctionIntro (Context.conjunctionRight hf₁) (Context.conjunctionRight hf₂))
    simpa [extendedMatrices, assumptions, namedBoth, Formula.not, Formula.encode, both, neg] using h
  have hc := Context.conjunctionLeft h0
  have hc' : Context Γ (PASoundness.PAtoCompactCandidateExact.candidateCode 2 81 77 78 72 64 73 59 75) := by
    simpa [candidate_formula_code] using hc
  simpa [Γ, result] using Context.mp hc' (Context.mp hmat (.closed fixed_product_equivalence))

def after_second_witness : KDerivation (imp guard3.encode result.encode) := by
  have helim := guarded_exists_left 41 guard3.encode secondMatrix.encode result.encode
    (free_vacuity 41 guard3 (by decide)) (result.vacuity 41 (by decide)) matrix_point
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [guard3.encode]
  have hg : Context Γ guard3.encode := .head _ _
  have hg' : Context Γ (both guard2.encode firstMatrix.encode) := by
    simpa [guard3, namedBoth, Formula.not, Formula.encode, both, neg] using hg
  have h2 : Context Γ (both guard1.encode targetMatrix.encode) := by
    simpa [guard2, namedBoth, Formula.not, Formula.encode, both, neg] using Context.conjunctionLeft hg'
  have h1 : Context Γ (both baseGuard.encode productMatrix.encode) := by
    simpa [guard1, namedBoth, Formula.not, Formula.encode, both, neg] using Context.conjunctionLeft h2
  have h0 : Context Γ (both (candidateFormula 2).encode
      (both targetProduct.encode (both firstEquivalent.encode secondEquivalent.encode))) := by
    simpa [baseGuard, namedBoth, Formula.not, Formula.encode, both, neg] using Context.conjunctionLeft h1
  have heq := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight h0))
  have hw := Context.mp heq (.closed second_matrix_exists)
  simpa [Γ] using Context.mp hw (Context.mp hg (.closed helim))

def after_first_witness : KDerivation (imp guard2.encode result.encode) := by
  have hpoint : KDerivation (imp guard2.encode (imp firstMatrix.encode result.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [firstMatrix.encode,guard2.encode]
    have hf : Context Γ firstMatrix.encode := .head _ _
    have hg : Context Γ guard2.encode := .hypothesis (by simp [Γ])
    have h3 : Context Γ guard3.encode := by
      simpa [guard3, namedBoth, Formula.not, Formula.encode, both, neg] using Context.conjunctionIntro hg hf
    simpa [Γ] using Context.mp h3 (.closed after_second_witness)
  have helim := guarded_exists_left 40 guard2.encode firstMatrix.encode result.encode
    (free_vacuity 40 guard2 (by decide)) (result.vacuity 40 (by decide)) hpoint
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [guard2.encode]
  have hg : Context Γ guard2.encode := .head _ _
  have h2 : Context Γ (both guard1.encode targetMatrix.encode) := by
    simpa [guard2, namedBoth, Formula.not, Formula.encode, both, neg] using hg
  have h1 : Context Γ (both baseGuard.encode productMatrix.encode) := by
    simpa [guard1, namedBoth, Formula.not, Formula.encode, both, neg] using Context.conjunctionLeft h2
  have h0 : Context Γ (both (candidateFormula 2).encode
      (both targetProduct.encode (both firstEquivalent.encode secondEquivalent.encode))) := by
    simpa [baseGuard, namedBoth, Formula.not, Formula.encode, both, neg] using Context.conjunctionLeft h1
  have heq := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight h0))
  have hw := Context.mp heq (.closed first_matrix_exists)
  simpa [Γ] using Context.mp hw (Context.mp hg (.closed helim))

def after_target_witness : KDerivation (imp guard1.encode result.encode) := by
  have hpoint : KDerivation (imp guard1.encode (imp targetMatrix.encode result.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [targetMatrix.encode,guard1.encode]
    have ht : Context Γ targetMatrix.encode := .head _ _
    have hg : Context Γ guard1.encode := .hypothesis (by simp [Γ])
    have h2 : Context Γ guard2.encode := by
      simpa [guard2, namedBoth, Formula.not, Formula.encode, both, neg] using Context.conjunctionIntro hg ht
    simpa [Γ] using Context.mp h2 (.closed after_first_witness)
  have helim := guarded_exists_left 45 guard1.encode targetMatrix.encode result.encode
    (free_vacuity 45 guard1 (by decide)) (result.vacuity 45 (by decide)) hpoint
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [guard1.encode]
  have hg : Context Γ guard1.encode := .head _ _
  have h1 : Context Γ (both baseGuard.encode productMatrix.encode) := by
    simpa [guard1, namedBoth, Formula.not, Formula.encode, both, neg] using hg
  have h0 : Context Γ (both (candidateFormula 2).encode
      (both targetProduct.encode (both firstEquivalent.encode secondEquivalent.encode))) := by
    simpa [baseGuard, namedBoth, Formula.not, Formula.encode, both, neg] using Context.conjunctionLeft h1
  have hp := Context.conjunctionLeft (Context.conjunctionRight h0)
  have hw := Context.mp hp (.closed target_matrix_exists)
  simpa [Γ] using Context.mp hw (Context.mp hg (.closed helim))

def source_matrix_point : KDerivation (imp baseGuard.encode (imp productMatrix.encode result.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [productMatrix.encode,baseGuard.encode]
  have hp : Context Γ productMatrix.encode := .head _ _
  have hg : Context Γ baseGuard.encode := .hypothesis (by simp [Γ])
  have h1 : Context Γ guard1.encode := by
    simpa [guard1, namedBoth, Formula.not, Formula.encode, both, neg] using Context.conjunctionIntro hg hp
  simpa [Γ] using Context.mp h1 (.closed after_target_witness)

/-- The source candidate, both product formulas and both factor-equivalence
formulas imply quotient equivalence of the two fixed-label product outputs. -/
def fixed_product_congruence : KDerivation (imp productFormula.encode (imp baseGuard.encode result.encode)) := by
  have helim := guarded_exists_left 6 baseGuard.encode productMatrix.encode result.encode
    (free_vacuity 6 baseGuard (by decide)) (result.vacuity 6 (by decide)) source_matrix_point
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [baseGuard.encode,productFormula.encode]
  have hg : Context Γ baseGuard.encode := .head _ _
  have hp : Context Γ productFormula.encode := .hypothesis (by simp [Γ])
  have hp' : Context Γ (existsCode 6 productMatrix.encode) := by simpa [productFormula, Formula.encode] using hp
  simpa [Γ] using Context.mp hp' (Context.mp hg (.closed helim))

theorem fixed_product_congruence_certificate : theoremCode (certificate fixed_product_congruence) =
    imp productFormula.encode (imp baseGuard.encode result.encode) := certificate_correct _

end PASoundness.PAtoCompactProductMatchCongruenceFixed

#print axioms PASoundness.PAtoCompactProductMatchCongruenceFixed.matrix_point
#print axioms PASoundness.PAtoCompactProductMatchCongruenceFixed.after_second_witness
#print axioms PASoundness.PAtoCompactProductMatchCongruenceFixed.after_first_witness
#print axioms PASoundness.PAtoCompactProductMatchCongruenceFixed.after_target_witness
#print axioms PASoundness.PAtoCompactProductMatchCongruenceFixed.source_matrix_point
#print axioms PASoundness.PAtoCompactProductMatchCongruenceFixed.fixed_product_congruence
#print axioms PASoundness.PAtoCompactProductMatchCongruenceFixed.fixed_product_congruence_certificate
