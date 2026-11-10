import PASoundness.PeanoInverseProductBounded
import PASoundness.PeanoOrderAsymmetry

/-! One changing-lower-bound step for PA inverse families. All input families
are explicit assumptions; this module does not establish bounded CRT. -/
namespace PASoundness.PeanoInverseFutureStep
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoInverseProductBounded

/-- Name 3 is the future index, 10 the current index, and 11 the upper bound.
The old invariant includes all indices j with j≥k and j<N. -/
def oldGuard : Peano.Formula :=
  (less (.var 3) (.var 10)).not ⊓ less (.var 3) (.var 11)

/-- After processing k, only strict future indices k<j<N remain. -/
def nextGuard : Peano.Formula :=
  (less (.var 10) (.var 3)) ⊓ less (.var 3) (.var 11)

/-- Standard meanings of the two literal guards, recorded separately from
the syntactic PA derivations below. -/
theorem oldGuard_realize (ρ : Nat → Nat) :
    oldGuard.Realize ρ ↔ ρ 10 ≤ ρ 3 ∧ ρ 3 < ρ 11 := by
  simp [oldGuard]

theorem nextGuard_realize (ρ : Nat → Nat) :
    nextGuard.Realize ρ ↔ ρ 10 < ρ 3 ∧ ρ 3 < ρ 11 := by
  simp [nextGuard]

def oldInverseFamily : Peano.Formula := FOL.allAt 3 (oldGuard.imp firstInverse)
def restrictedInverseFamily : Peano.Formula := FOL.allAt 3 (nextGuard.imp firstInverse)
def newModulusInverseFamily : Peano.Formula := FOL.allAt 3 (nextGuard.imp secondInverse)
def updatedInverseFamily : Peano.Formula := FOL.allAt 3 (nextGuard.imp productInverse)

/-- Restrict the old inverse family from `j≥k` to `j>k`. This uses a PA
order-asymmetry derivation, not external arithmetic truth. -/
theorem restrict_to_strict_future :
    FormulaProves (oldInverseFamily.imp restrictedInverseFamily) := by
  let Γ := [nextGuard, oldInverseFamily]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.generalize 3
  · intro ψ hψ
    have h : ψ = oldInverseFamily := by simpa using hψ
    subst ψ
    simp [oldInverseFamily]
  apply FOL.Context.deduction
  have hn : FOL.Context Peano.Axiom Γ nextGuard := FOL.Context.head _ _
  have hold : FOL.Context Peano.Axiom Γ oldInverseFamily :=
    FOL.Context.under (FOL.Context.head [] oldInverseFamily) nextGuard
  have hlt : FOL.Context Peano.Axiom Γ (less (.var 10) (.var 3)) :=
    FOL.Context.conjunctionLeft hn
  have hupp : FOL.Context Peano.Axiom Γ (less (.var 3) (.var 11)) :=
    FOL.Context.conjunctionRight hn
  have hnot : FOL.Context Peano.Axiom Γ (less (.var 3) (.var 10)).not :=
    .mp (.closed (PeanoOrderAsymmetry.less_asymmetric_all (.var 10) (.var 3))) hlt
  have hguard : FOL.Context Peano.Axiom Γ oldGuard := FOL.Context.conjunctionIntro hnot hupp
  exact .mp (FOL.Context.allSelf hold) hguard

def boundaryFactor : Peano.Term := modulus (.var 2) (.var 10)
def targetSecondBody : Peano.Formula :=
  (mul boundaryFactor (.var 6)).equal
    (add (succ zero) (mul (.var 7) (modulus (.var 2) (.var 3))))
def targetProductMatrix (u v : Peano.Term) : Peano.Formula :=
  (mul (mul (.var 0) boundaryFactor) u).equal
    (add (succ zero) (mul v (modulus (.var 2) (.var 3))))
def targetSecond : Peano.Formula := FOL.existsAt 6 (FOL.existsAt 7 targetSecondBody)
def targetProduct : Peano.Formula := FOL.existsAt 8 (FOL.existsAt 9 (targetProductMatrix (.var 8) (.var 9)))

theorem first_sub : FOL.substAt firstInverse 1 boundaryFactor = firstInverse := by
  simp [FOL.substAt, firstInverse, firstBody, boundaryFactor, modulus, FOL.existsAt, FOL.allAt,
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

theorem second_sub : FOL.substAt secondInverse 1 boundaryFactor = targetSecond := by
  simp [FOL.substAt, secondInverse, secondBody, boundaryFactor, targetSecond, targetSecondBody,
    modulus, FOL.existsAt, FOL.allAt,
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

theorem product_sub : FOL.substAt productInverse 1 boundaryFactor = targetProduct := by
  simp [FOL.substAt, productInverse, productBody, productMatrix, boundaryFactor, targetProduct, targetProductMatrix,
    modulus, FOL.existsAt, FOL.allAt,
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

theorem specialize_boundary :
    FormulaProves (firstInverse.imp (targetSecond.imp targetProduct)) := by
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom)
      (.allElim (firstInverse.imp (secondInverse.imp productInverse)) 1 boundaryFactor))
    (FOL.Derivation.generalize 1 product_inverse)
  change FormulaProves ((FOL.substAt firstInverse 1 boundaryFactor).imp
    ((FOL.substAt secondInverse 1 boundaryFactor).imp (FOL.substAt productInverse 1 boundaryFactor))) at h
  simpa only [first_sub, second_sub, product_sub] using h

/-- Given the old inverse family and an inverse family for the newly included
factor on strict future indices, update the product inverse family and drop the
processed index. Name 1 is that factor; identifying it with the current beta
modulus is a separate syntactic specialization or explicit equality premise. -/
theorem future_product_step : FormulaProves
    (oldInverseFamily.imp (newModulusInverseFamily.imp updatedInverseFamily)) := by
  let Γ := [newModulusInverseFamily, oldInverseFamily]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hold : FOL.Context Peano.Axiom Γ oldInverseFamily :=
    FOL.Context.under (FOL.Context.head [] oldInverseFamily) newModulusInverseFamily
  have hnew : FOL.Context Peano.Axiom Γ newModulusInverseFamily := FOL.Context.head _ _
  have hrestrict : FOL.Context Peano.Axiom Γ restrictedInverseFamily :=
    .mp (.closed restrict_to_strict_future) hold
  exact .mp (.mp (.closed (bounded_inverse_product nextGuard)) hrestrict) hnew

/-- The actual current beta modulus is the new factor. With inverse families
on the old and strict-future ranges as explicit PA hypotheses, the updated
product has inverse witnesses at every remaining future index. This does not
construct either input family. -/
theorem future_beta_modulus_step : FormulaProves
    (oldInverseFamily.imp ((FOL.allAt 3 (nextGuard.imp targetSecond)).imp
      (FOL.allAt 3 (nextGuard.imp targetProduct)))) := by
  let Q := FOL.allAt 3 (nextGuard.imp targetSecond)
  let Γ := [nextGuard, Q, oldInverseFamily]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.generalize 3
  · intro ψ hψ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hψ
    rcases hψ with rfl | rfl <;> simp [oldInverseFamily]
  apply FOL.Context.deduction
  have hg : FOL.Context Peano.Axiom Γ nextGuard := FOL.Context.head _ _
  have hold : FOL.Context Peano.Axiom Γ oldInverseFamily := .hypothesis (by simp [Γ])
  have hpair : FOL.Context Peano.Axiom Γ Q := .hypothesis (by simp [Γ])
  have hfirstall : FOL.Context Peano.Axiom Γ restrictedInverseFamily :=
    .mp (.closed restrict_to_strict_future) hold
  have hfirst : FOL.Context Peano.Axiom Γ firstInverse :=
    .mp (FOL.Context.allSelf hfirstall) hg
  have hsecond : FOL.Context Peano.Axiom Γ targetSecond :=
    .mp (FOL.Context.allSelf hpair) hg
  exact .mp (.mp (.closed specialize_boundary) hfirst) hsecond

end PASoundness.PeanoInverseFutureStep
