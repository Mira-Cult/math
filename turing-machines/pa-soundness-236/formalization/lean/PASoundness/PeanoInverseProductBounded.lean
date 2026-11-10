import PASoundness.PeanoInverseProduct
import PASoundness.PeanoBitPositionReduction

/-! Existential inverse certificates and their bounded-future product step.
All assumptions are object-level PA formulas; no certificates or CRT solution
are asserted to exist by the pointwise packaging rules. -/
namespace PASoundness.PeanoInverseProductBounded
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic

/-- Name 0 is the current product, 1 the newly processed modulus, 2 the beta
parameter, and name 3 the future index. Names 4,5 are inverse witnesses. -/
def firstBody : Peano.Formula :=
  (mul (.var 0) (.var 4)).equal
    (add (succ zero) (mul (.var 5) (modulus (.var 2) (.var 3))))

/-- Names 6,7 are inverse witnesses for the newly processed modulus. -/
def secondBody : Peano.Formula :=
  (mul (.var 1) (.var 6)).equal
    (add (succ zero) (mul (.var 7) (modulus (.var 2) (.var 3))))

/-- Matrix for inverse witnesses of the updated product. -/
def productMatrix (u v : Peano.Term) : Peano.Formula :=
  (mul (mul (.var 0) (.var 1)) u).equal
    (add (succ zero) (mul v (modulus (.var 2) (.var 3))))

/-- Names 8,9 are inverse witnesses for the updated product. -/
def productBody : Peano.Formula := productMatrix (.var 8) (.var 9)

def firstInverse : Peano.Formula := FOL.existsAt 4 (FOL.existsAt 5 firstBody)
def secondInverse : Peano.Formula := FOL.existsAt 6 (FOL.existsAt 7 secondBody)
def productInverse : Peano.Formula := FOL.existsAt 8 (FOL.existsAt 9 productBody)

/-- Explicit witnesses from the inverse-product identity. -/
def productWitnessU : Peano.Term := mul (.var 4) (.var 6)
def productWitnessV : Peano.Term :=
  add (add (.var 7) (.var 5)) (mul (mul (.var 5) (.var 7)) (modulus (.var 2) (.var 3)))

/-- Package those explicit witnesses into the displayed existential formula. -/
theorem package_product_witnesses : FormulaProves
    ((productMatrix productWitnessU productWitnessV).imp productInverse) := by
  have hinner : FormulaProves ((productMatrix productWitnessU productWitnessV).imp
      (FOL.existsAt 9 (productMatrix productWitnessU (.var 9)))) := by
    have h := FOL.Derivation.existsIntro (A := Peano.Axiom)
      (productMatrix productWitnessU (.var 9)) 9 productWitnessV
    simpa [FOL.substAt, productMatrix, productWitnessU, productWitnessV, modulus,
      FOL.equality_subst, add_subst, mul_subst, succ_subst, PeanoArithmetic.zero_subst,
      FirstOrder.Language.Term.subst] using h
  have he : FOL.substAt (FOL.existsAt 9 (productMatrix (.var 8) (.var 9))) 8 productWitnessU =
      FOL.existsAt 9 (productMatrix productWitnessU (.var 9)) := by
    simp [FOL.substAt, productMatrix, productWitnessU, modulus, FOL.existsAt, FOL.allAt,
      Peano.add, Peano.mul, Peano.succ, Peano.zero, FirstOrder.Language.Term.equal,
      FirstOrder.Language.Term.bdEqual, FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
      FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
      FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
      FirstOrder.Language.BoundedFormula.relabelAux]
    repeat' first
      | rfl
      | constructor
      | (congr 1; funext i; fin_cases i <;>
          dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])
  have houter : FormulaProves ((FOL.existsAt 9 (productMatrix productWitnessU (.var 9))).imp
      productInverse) := by
    have h := FOL.Derivation.existsIntro (A := Peano.Axiom)
      (FOL.existsAt 9 (productMatrix (.var 8) (.var 9))) 8 productWitnessU
    rw [he] at h
    simpa only [productInverse, productBody] using h
  exact FOL.Derivation.compose hinner houter

/-- The two explicit inverse equations imply the existential product inverse. -/
theorem inverse_product_matrix :
    FormulaProves (firstBody.imp (secondBody.imp productInverse)) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have ha : FOL.Context Peano.Axiom [secondBody, firstBody] firstBody :=
    FOL.Context.under (FOL.Context.head [] firstBody) secondBody
  have hb : FOL.Context Peano.Axiom [secondBody, firstBody] secondBody := FOL.Context.head _ _
  have hm : FOL.Context Peano.Axiom [secondBody, firstBody]
      (productMatrix productWitnessU productWitnessV) :=
    .mp (.mp (.closed (PeanoInverseProduct.inverse_product
      (.var 0) (.var 1) (.var 4) (.var 6) (.var 5) (.var 7)
      (modulus (.var 2) (.var 3)))) ha) hb
  exact .mp (.closed package_product_witnesses) hm

private theorem swap_antecedents {L : Language} {A : FOL.Formula L → Prop}
    {φ ψ χ : FOL.Formula L} (h : FOL.Derivation A (φ.imp (ψ.imp χ))) :
    FOL.Derivation A (ψ.imp (φ.imp χ)) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hφ : FOL.Context A [φ, ψ] φ := FOL.Context.head _ _
  have hψ : FOL.Context A [φ, ψ] ψ := FOL.Context.under (FOL.Context.head [] ψ) φ
  exact .mp (.mp (.closed h) hφ) hψ

/-- Four freshness-checked existential eliminations package a proof of the
matrix implication into a proof using two existential inverse certificates.
The supplied matrix derivation remains an explicit premise of this lemma. -/
theorem product_inverse_of_matrix
    (h : FormulaProves (firstBody.imp (secondBody.imp productInverse))) :
    FormulaProves (firstInverse.imp (secondInverse.imp productInverse)) := by
  have hf7 : 7 ∉ (firstBody.imp productInverse).freeVarFinset := by decide
  have h7 := PeanoBitPositionReduction.exists_elim 7 hf7 (swap_antecedents h)
  have hf6 : 6 ∉ (firstBody.imp productInverse).freeVarFinset := by decide
  have h6 := PeanoBitPositionReduction.exists_elim 6 hf6 h7
  have hswap : FormulaProves (firstBody.imp (secondInverse.imp productInverse)) := by
    exact swap_antecedents h6
  have hf5 : 5 ∉ (secondInverse.imp productInverse).freeVarFinset := by decide
  have h5 := PeanoBitPositionReduction.exists_elim 5 hf5 hswap
  have hf4 : 4 ∉ (secondInverse.imp productInverse).freeVarFinset := by decide
  have h4 := PeanoBitPositionReduction.exists_elim 4 hf4 h5
  exact h4

/-- Quantify the existential product rule over any common guard on the future
index. The premises and conclusion bind name 3; the guard is an arbitrary PA
formula and can express the interval of unprocessed indices. -/
theorem bounded_product_of_matrix (guard : Peano.Formula)
    (h : FormulaProves (firstBody.imp (secondBody.imp productInverse))) :
    FormulaProves
      ((FOL.allAt 3 (guard.imp firstInverse)).imp
        ((FOL.allAt 3 (guard.imp secondInverse)).imp
          (FOL.allAt 3 (guard.imp productInverse)))) := by
  let F := FOL.allAt 3 (guard.imp firstInverse)
  let G := FOL.allAt 3 (guard.imp secondInverse)
  let Γ := [guard, G, F]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.generalize 3
  · intro ψ hψ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hψ
    rcases hψ with rfl | rfl <;> simp
  apply FOL.Context.deduction
  have hg : FOL.Context Peano.Axiom Γ guard := FOL.Context.head _ _
  have hf : FOL.Context Peano.Axiom Γ F := .hypothesis (by simp [Γ])
  have hs : FOL.Context Peano.Axiom Γ G := .hypothesis (by simp [Γ])
  have hfirst : FOL.Context Peano.Axiom Γ firstInverse := .mp (FOL.Context.allSelf hf) hg
  have hsecond : FOL.Context Peano.Axiom Γ secondInverse := .mp (FOL.Context.allSelf hs) hg
  exact .mp (.mp (.closed (product_inverse_of_matrix h)) hfirst) hsecond

/-- Existential inverse certificates for two factors yield one for their
product. The modulus is the exact beta modulus at the displayed future index. -/
theorem product_inverse :
    FormulaProves (firstInverse.imp (secondInverse.imp productInverse)) :=
  product_inverse_of_matrix inverse_product_matrix

/-- Pointwise in any guarded family of future indices, two existential inverse
families give an existential inverse family for the product. This does not
construct the two input families or a bounded CRT solution. -/
theorem bounded_inverse_product (guard : Peano.Formula) :
    FormulaProves
      ((FOL.allAt 3 (guard.imp firstInverse)).imp
        ((FOL.allAt 3 (guard.imp secondInverse)).imp
          (FOL.allAt 3 (guard.imp productInverse)))) :=
  bounded_product_of_matrix guard inverse_product_matrix

end PASoundness.PeanoInverseProductBounded
