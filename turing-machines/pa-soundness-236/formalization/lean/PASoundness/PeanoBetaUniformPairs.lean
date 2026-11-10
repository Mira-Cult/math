import PASoundness.PeanoBetaPairDivisible
import PASoundness.PeanoCommonPositive

/-! PA constructs a positive parameter above an arbitrary bound with inverse
certificates for every beta-modulus pair `(i, i+S k)` whose upper index is at
most N, retaining the bounded common-divisor property. The proof gives a fixed-name formula and its universal closure. It does
not construct simultaneous beta rows or establish bounded CRT. -/
namespace PASoundness.PeanoBetaUniformPairs
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoDivisibility
open PeanoBetaPairDivisible

/-- The divisor condition from the positive common-multiple matrix, with N at
name 7 and parameter C at name 1. -/
def boundedDivisors : Peano.Formula :=
  FOL.allAt 4 ((less zero (.var 4)).imp
    ((less (.var 4) (succ (.var 7))).imp (divides (.var 4) (.var 1))))

private theorem divides_subst (k d : Peano.Term) (σ : Nat → Peano.Term) :
    (divides k d).subst σ = divides (k.subst σ) (d.subst σ) := by
  unfold divides
  rw [SyntaxTransport.formula_subst_comp]
  congr 1
  funext y
  by_cases h0 : y = 0 <;> by_cases h1 : y = 1 <;> simp [h0, h1]

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := by rfl

/-- Instantiate the bounded divisor property at the positive gap `S k` and
apply the existing PA pair-inverse theorem. Free names are i=0, C=1, k=2,
and N=7; inverse witnesses are bound by `inverseTemplate`. -/
theorem inverse_of_bounded_gap :
    FormulaProves (boundedDivisors.imp ((less zero (.var 1)).imp
      ((less (succ (.var 2)) (succ (.var 7))).imp inverseTemplate))) := by
  let A := boundedDivisors
  let P := less zero (.var 1)
  let L := less (succ (.var 2)) (succ (.var 7))
  let D := divides (succ (.var 2)) (.var 1)
  let body := (less zero (.var 4)).imp
    ((less (.var 4) (succ (.var 7))).imp (divides (.var 4) (.var 1)))
  have inst : FormulaProves (A.imp ((less zero (succ (.var 2))).imp (L.imp D))) := by
    have h := FOL.Derivation.logical (Axiom := Peano.Axiom)
      (FOL.LogicalAxiom.allElim body 4 (succ (.var 2)))
    simpa only [A, boundedDivisors, body, FOL.substAt,
      subst_imp, less_subst, divides_subst,
      PeanoArithmetic.zero_subst, succ_subst, FirstOrder.Language.Term.subst,
      ↓reduceIte, show (7 : Nat) ≠ 4 by decide, show (1 : Nat) ≠ 4 by decide]
      using h
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have ha : FOL.Context Peano.Axiom [L,P,A] A :=
    FOL.Context.under (FOL.Context.under (FOL.Context.head [] A) P) L
  have hp : FOL.Context Peano.Axiom [L,P,A] P :=
    FOL.Context.under (FOL.Context.head [A] P) L
  have hl : FOL.Context Peano.Axiom [L,P,A] L := FOL.Context.head _ _
  have hd : FOL.Context Peano.Axiom [L,P,A] D :=
    .mp (.mp (.mp (.closed inst) ha)
      (.closed (PeanoOrderTotality.zero_less_succ (.var 2)))) hl
  exact .mp (.mp (.closed divisible_positive_inverse_vars) hd) hp

/-- For one positive parameter and one bounded-divisor hypothesis, the
preceding PA derivation holds uniformly for every index and every bounded
positive gap. This does not claim that a common parameter or a CRT code exists. -/
theorem uniform_inverse_of_bounded_gap :
    FormulaProves (boundedDivisors.imp ((less zero (.var 1)).imp
      (FOL.allAt 0 (FOL.allAt 2
        ((less (succ (.var 2)) (succ (.var 7))).imp inverseTemplate))))) := by
  let A := boundedDivisors
  let P := less zero (.var 1)
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.generalize 0
  · intro φ hφ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl <;> decide
  apply FOL.Context.generalize 2
  · intro φ hφ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl <;> decide
  have ha : FOL.Context Peano.Axiom [P,A] A := FOL.Context.under (FOL.Context.head [] A) P
  have hp : FOL.Context Peano.Axiom [P,A] P := FOL.Context.head [A] P
  exact .mp (.mp (.closed inverse_of_bounded_gap) ha) hp

private theorem or_elim {L : Language} {A : FOL.Formula L → Prop}
    {Γ : List (FOL.Formula L)} {φ ψ χ : FOL.Formula L}
    (h : FOL.Context A Γ (φ ⊔ ψ)) (hφ : FOL.Context A Γ (φ.imp χ))
    (hψ : FOL.Context A Γ (ψ.imp χ)) : FOL.Context A Γ χ := by
  apply FOL.Context.dne
  apply FOL.Context.deduction
  have hnφ : FOL.Context A (χ.not :: Γ) φ.not :=
    .mp (FOL.Context.under (FOL.Context.contrapose hφ) χ.not) (FOL.Context.head Γ χ.not)
  have hψ' : FOL.Context A (χ.not :: Γ) ψ :=
    .mp (FOL.Context.under h χ.not) hnφ
  exact .mp (FOL.Context.head Γ χ.not) (.mp (FOL.Context.under hψ χ.not) hψ')

/-- Discarding a nonnegative summand preserves a strict upper bound. -/
theorem drop_add_left (i d n : Peano.Term) :
    FormulaProves ((less (add i d) n).imp (less d n)) := by
  let H := less (add i d) n
  let E := zero.equal i
  let P := less zero i
  let Q := less i zero
  let T := less d n
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have hE : FOL.Context Peano.Axiom [H] (E.imp T) := by
    apply FOL.Context.deduction
    have he : FOL.Context Peano.Axiom [E, H] E := FOL.Context.head _ _
    have heq : FOL.Context Peano.Axiom [E, H] ((add i d).equal d) := by
      apply PeanoPolynomialContext.cls_exact
      have hi : PeanoPolynomialContext.cls [E,H] i = PeanoPolynomialContext.cls [E,H] zero := (PeanoPolynomialContext.cls_sound he).symm
      simp only [PeanoPolynomialContext.cls_add, PeanoPolynomialContext.cls_zero, hi]
      exact _root_.zero_add _
    exact .mp (.mp (.closed (PeanoQuotientGap.less_left_congr (add i d) d n)) heq)
      (FOL.Context.under (FOL.Context.head [] H) E)
  have hP : FOL.Context Peano.Axiom [H] (P.imp T) := by
    apply FOL.Context.deduction
    have hp : FOL.Context Peano.Axiom [P,H] P := FOL.Context.head _ _
    have hh : FOL.Context Peano.Axiom [P,H] H := FOL.Context.under (FOL.Context.head [] H) P
    have hh₁ : FOL.Context Peano.Axiom [P,H] (less (add d zero) (add d i)) :=
      .mp (.closed (PeanoMultiplyQuotientStep.less_add_left zero i d)) hp
    have h₁ : FOL.Context Peano.Axiom [P,H] (less d (add i d)) := by
      have hleft : FOL.Context Peano.Axiom [P,H] ((add d zero).equal d) :=
        .closed (.axiom (.add_zero d))
      have hright : FOL.Context Peano.Axiom [P,H] ((add d i).equal (add i d)) :=
        .closed (PeanoAdditionAssociative.add_comm d i)
      have ht : FOL.Context Peano.Axiom [P,H] (less d (add d i)) :=
        .mp (.mp (.closed (PeanoQuotientGap.less_left_congr (add d zero) d (add d i))) hleft) hh₁
      exact .mp (.mp (.closed (PeanoMultiplyQuotientStep.less_right_congr d (add d i) (add i d))) hright) ht
    exact .mp (.mp (.closed (PeanoOrderTransitive.less_transitive_all d (add i d) n)) h₁) hh
  have hQ : FOL.Context Peano.Axiom [H] (Q.imp T) := by
    apply FOL.Context.deduction
    exact FOL.Context.explode T (.mp (.closed (PeanoEmptyBitSet.no_less_zero i)) (FOL.Context.head _ _))
  have hEP : FOL.Context Peano.Axiom [H] ((E ⊔ P).imp T) := by
    apply FOL.Context.deduction
    exact or_elim (FOL.Context.head [H] (E ⊔ P))
      (FOL.Context.under hE (E ⊔ P)) (FOL.Context.under hP (E ⊔ P))
  exact or_elim (.closed (PeanoOrderTotality.trichotomy_all zero i)) hEP hQ


/-- A bounded upper index also bounds its positive gap, so every pair of the
form `(i, i+S k)` with upper index at most N has inverse witnesses. -/
theorem inverse_of_bounded_upper_index :
    FormulaProves (boundedDivisors.imp ((less zero (.var 1)).imp
      ((less (add (.var 0) (succ (.var 2))) (succ (.var 7))).imp inverseTemplate))) := by
  let A := boundedDivisors
  let P := less zero (.var 1)
  let U := less (add (.var 0) (succ (.var 2))) (succ (.var 7))
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have ha : FOL.Context Peano.Axiom [U,P,A] A :=
    FOL.Context.under (FOL.Context.under (FOL.Context.head [] A) P) U
  have hp : FOL.Context Peano.Axiom [U,P,A] P :=
    FOL.Context.under (FOL.Context.head [A] P) U
  have hu : FOL.Context Peano.Axiom [U,P,A] U := FOL.Context.head _ _
  have hl : FOL.Context Peano.Axiom [U,P,A] (less (succ (.var 2)) (succ (.var 7))) :=
    .mp (.closed (drop_add_left (.var 0) (succ (.var 2)) (succ (.var 7)))) hu
  exact .mp (.mp (.mp (.closed inverse_of_bounded_gap) ha) hp) hl

/-- Uniform PA version of `inverse_of_bounded_upper_index`. -/
theorem uniform_inverse_of_bounded_upper_index :
    FormulaProves (boundedDivisors.imp ((less zero (.var 1)).imp
      (FOL.allAt 0 (FOL.allAt 2
        ((less (add (.var 0) (succ (.var 2))) (succ (.var 7))).imp inverseTemplate))))) := by
  let A := boundedDivisors
  let P := less zero (.var 1)
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.generalize 0
  · intro φ hφ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl <;> decide
  apply FOL.Context.generalize 2
  · intro φ hφ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl <;> decide
  have ha : FOL.Context Peano.Axiom [P,A] A := FOL.Context.under (FOL.Context.head [] A) P
  have hp : FOL.Context Peano.Axiom [P,A] P := FOL.Context.head [A] P
  exact .mp (.mp (.closed inverse_of_bounded_upper_index) ha) hp

/-- The fixed-name matrix records a positive parameter above R and uniform
inverse certificates for all pairs whose upper index is at most N. -/
def uniformPairBody : Peano.Formula :=
  (less (.var 8) (.var 1)) ⊓ ((less zero (.var 1)) ⊓ (boundedDivisors ⊓
    FOL.allAt 0 (FOL.allAt 2
      ((less (add (.var 0) (succ (.var 2))) (succ (.var 7))).imp inverseTemplate))))

def uniformPairExists : Peano.Formula := FOL.existsAt 1 uniformPairBody

private theorem positiveCommon_syntax :
    PeanoCommonPositive.positiveCommon (.var 7) (.var 8) =
      FOL.existsAt 1 (PeanoCommonPositive.positiveBody (.var 7) (.var 8) (.var 1)) := by
  simp [PeanoCommonPositive.positiveCommon, PeanoCommonPositive.positiveTemplate,
    PeanoCommonPositive.positiveBody, divides, dividesTemplate, FOL.existsAt, FOL.allAt,
    less, lessTemplate, exAt, v, Peano.add, Peano.mul, Peano.succ, Peano.zero,
    FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux, Min.min]
  repeat' first
    | rfl
    | constructor
    | (congr 1; funext i; fin_cases i <;>
        dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])

/-- PA constructs a positive common parameter above R with simultaneous
pairwise inverse certificates through the supplied bound N. The pair indices
are represented as `i` and `i+S k`. No simultaneous beta rows are asserted. -/
theorem uniform_pair_parameter_exists_vars : FormulaProves uniformPairExists := by
  let B := PeanoCommonPositive.positiveBody (.var 7) (.var 8) (.var 1)
  let H := less (.var 8) (.var 1)
  let P := less zero (.var 1)
  let U := FOL.allAt 0 (FOL.allAt 2
    ((less (add (.var 0) (succ (.var 2))) (succ (.var 7))).imp inverseTemplate))
  have hbody : FormulaProves (B.imp uniformPairExists) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have hb : FOL.Context Peano.Axiom [B] B := FOL.Context.head [] B
    have hh : FOL.Context Peano.Axiom [B] H := FOL.Context.conjunctionLeft hb
    have hp : FOL.Context Peano.Axiom [B] P :=
      FOL.Context.conjunctionLeft (FOL.Context.conjunctionRight hb)
    have hd : FOL.Context Peano.Axiom [B] boundedDivisors :=
      FOL.Context.conjunctionRight (FOL.Context.conjunctionRight hb)
    have hu : FOL.Context Peano.Axiom [B] U :=
      .mp (.mp (.closed uniform_inverse_of_bounded_upper_index) hd) hp
    have hpair : FOL.Context Peano.Axiom [B] uniformPairBody :=
      FOL.Context.conjunctionIntro hh
        (FOL.Context.conjunctionIntro hp (FOL.Context.conjunctionIntro hd hu))
    have hi : FormulaProves (uniformPairBody.imp uniformPairExists) := by
      simpa only [uniformPairExists, SyntaxTransport.substAt_self] using
        (FOL.Derivation.existsIntro (A := Peano.Axiom) uniformPairBody 1 (.var 1))
    exact .mp (.closed hi) hpair
  have hf : 1 ∉ uniformPairExists.freeVarFinset := by decide
  have hex := PeanoBitPositionReduction.exists_elim 1 hf hbody
  have hc : FormulaProves (FOL.existsAt 1 B) := by
    have h := PeanoCommonPositive.positive_common_exists (.var 7) (.var 8)
    rwa [positiveCommon_syntax] at h
  exact .mp hex hc

/-- Universal closure of the fixed-name common-parameter theorem. -/
theorem uniform_pair_parameter_exists :
    FormulaProves (FOL.allAt 7 (FOL.allAt 8 uniformPairExists)) :=
  .generalize 7 (.generalize 8 uniform_pair_parameter_exists_vars)

end PASoundness.PeanoBetaUniformPairs
