import PASoundness.PeanoPowerDivisibilityClosed
import PASoundness.PeanoPowerDivisibilityBoundary
import PASoundness.PeanoCommonPositive
import PASoundness.PeanoPositiveFactor
import PASoundness.PeanoBetaPairDivisible

/-! Object-level PA comparisons of literal power traces. -/
namespace PASoundness.PeanoPowerMonotonic
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic PeanoDivisibility
open PeanoPolynomialContext PeanoCommonPositive.Predecessor

private theorem divides_syntax :
    divides (add (.var 2) (.var 2)) (.var 6) = FOL.existsAt 7
      ((.var 6 : Peano.Term).equal (mul (.var 7) (add (.var 2) (.var 2)))) := by
  simp [divides, dividesTemplate, FOL.existsAt, FOL.allAt,
    Peano.mul, Peano.add, Peano.zero, FirstOrder.Language.Term.equal,
    FirstOrder.Language.Term.bdEqual, FirstOrder.Language.Term.subst,
    FirstOrder.Language.Term.relabel, FirstOrder.Language.BoundedFormula.not,
    FirstOrder.Language.BoundedFormula.subst, FirstOrder.Language.BoundedFormula.relabel,
    FirstOrder.Language.BoundedFormula.mapTermRel, FirstOrder.Language.BoundedFormula.relabelAux]
  repeat' first
    | rfl
    | constructor
    | (congr 1; funext i; fin_cases i <;>
        dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])

private theorem predecessor_syntax : hasPredecessor (.var 7) = FOL.existsAt 8
    ((.var 7 : Peano.Term).equal (succ (.var 8))) := by
  simp [hasPredecessor, predecessorTemplate, FOL.existsAt, FOL.allAt,
    Peano.succ, Peano.zero, FirstOrder.Language.Term.equal,
    FirstOrder.Language.Term.bdEqual, FirstOrder.Language.Term.subst,
    FirstOrder.Language.Term.relabel, FirstOrder.Language.BoundedFormula.not,
    FirstOrder.Language.BoundedFormula.subst, FirstOrder.Language.BoundedFormula.relabel,
    FirstOrder.Language.BoundedFormula.mapTermRel, FirstOrder.Language.BoundedFormula.relabelAux]
  rfl

/-- Positive u and q, plus (u+u)|q, entail u<q. -/
theorem strict_from_doubled_divisor : FormulaProves
    ((less zero (.var 2)).imp ((less zero (.var 6)).imp
      ((divides (add (.var 2) (.var 2)) (.var 6)).imp
        (less (.var 2) (.var 6))))) := by
  let u : Peano.Term := .var 2
  let q : Peano.Term := .var 6
  let z : Peano.Term := .var 7
  let t : Peano.Term := .var 8
  let d := add u u
  let P := less zero u
  let Q := less zero q
  let E := q.equal (mul z d)
  let H := z.equal (succ t)
  let T := less u q
  have hEq : FormulaProves (H.imp (E.imp (P.imp T))) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    let Γ := [P,E,H]
    have hp : FOL.Context Peano.Axiom Γ P := .head _ _
    have he : FOL.Context Peano.Axiom Γ E := .hypothesis (by simp [Γ])
    have hh : FOL.Context Peano.Axiom Γ H := .hypothesis (by simp [Γ])
    have hm : FOL.Context Peano.Axiom Γ (q.equal (add d (mul t d))) := by
      apply cls_exact
      have he' : cls Γ q = cls Γ z * cls Γ d := by simpa only [cls_mul] using cls_sound he
      have hh' : cls Γ z = cls Γ (succ t) := cls_sound hh
      simp only [cls_add, cls_mul]
      rw [he', hh']
      simp only [PeanoBetaPairDivisible.contextual_cls_succ]
      ring
    have h0 : FOL.Context Peano.Axiom Γ (less (add u zero) (add u u)) :=
      .mp (.closed (PeanoMultiplyQuotientStep.less_add_left zero u u)) hp
    have h1 : FOL.Context Peano.Axiom Γ (less u d) :=
      .mp (.mp (.closed (PeanoQuotientGap.less_left_congr (add u zero) u d))
        (.closed (.axiom (.add_zero u)))) h0
    have h2 : FOL.Context Peano.Axiom Γ (less u (add d (mul t d))) :=
      .mp (.closed (PeanoQuotientGap.less_add_right u d (mul t d))) h1
    exact .mp (.mp (.closed (PeanoMultiplyQuotientStep.less_right_congr
      u (add d (mul t d)) q)) (FOL.Context.eqSymm hm)) h2
  have ht : 8 ∉ (E.imp (P.imp T)).freeVarFinset := by decide
  have hp' : FormulaProves ((hasPredecessor z).imp (E.imp (P.imp T))) := by
    simpa only [predecessor_syntax, z, H] using PeanoBitPositionReduction.exists_elim 8 ht hEq
  have hz : FormulaProves (E.imp (Q.imp (P.imp T))) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    let Γ := [P,Q,E]
    have hp : FOL.Context Peano.Axiom Γ P := .head _ _
    have hq : FOL.Context Peano.Axiom Γ Q := .hypothesis (by simp [Γ])
    have he : FOL.Context Peano.Axiom Γ E := .hypothesis (by simp [Γ])
    have hz : FOL.Context Peano.Axiom Γ (less zero z) :=
      .mp (.mp (.closed (PeanoPositiveFactor.quotient_positive q z d)) hq) he
    have hpred : FOL.Context Peano.Axiom Γ (hasPredecessor z) :=
      .mp (.closed (positive_has_predecessor z)) hz
    exact .mp (.mp (.mp (.closed hp') hpred) he) hp
  have hf : 7 ∉ (Q.imp (P.imp T)).freeVarFinset := by decide
  have hdiv := PeanoBitPositionReduction.exists_elim 7 hf hz
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let D := divides (add (.var 2) (.var 2)) (.var 6)
  let Γ := [D,Q,P]
  have hp : FOL.Context Peano.Axiom Γ P := .hypothesis (by simp [Γ])
  have hq : FOL.Context Peano.Axiom Γ Q := .hypothesis (by simp [Γ])
  have hd : FOL.Context Peano.Axiom Γ D := .head _ _
  have hex : FOL.Context Peano.Axiom Γ (FOL.existsAt 7 E) := by simpa only [D, divides_syntax, E, z, d, u, q] using hd
  exact .mp (.mp (.mp (.closed hdiv) hex) hq) hp


/-- At equal indices, literal power uniqueness supplies the weak comparison. -/
theorem equal_index_le (i n u p : Peano.Term) : FormulaProves
    ((i.equal n).imp ((pow2 i u).imp ((pow2 n p).imp (less u (succ p))))) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let Γ := [pow2 n p, pow2 i u, i.equal n]
  have hi : FOL.Context Peano.Axiom Γ (i.equal n) := .hypothesis (by simp [Γ])
  have hu : FOL.Context Peano.Axiom Γ (pow2 i u) := .hypothesis (by simp [Γ])
  have hp : FOL.Context Peano.Axiom Γ (pow2 n p) := FOL.Context.head _ _
  have hu' : FOL.Context Peano.Axiom Γ (pow2 n u) :=
    .mp (.mp (.closed (PeanoPowerDivisibilityBoundary.power_index_congr i n u)) hi) hu
  have he : FOL.Context Peano.Axiom Γ (u.equal p) :=
    .mp (.mp (.closed (PeanoPowerUnique.power_unique n u p)) hu') hp
  have hes : FOL.Context Peano.Axiom Γ ((succ u).equal (succ p)) :=
    .mp (.closed (PeanoOrderIrreflexive.succ_congr u p)) he
  exact .mp (.mp (.closed (PeanoMultiplyQuotientStep.less_right_congr u (succ u) (succ p))) hes)
    (.closed (PeanoPowerTransition.self_less_succ u))

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

/-- Strict order of the indices implies strict order of the literal powers.
Names 1 and 0 are the smaller and larger indices, and 2 and 6 their values. -/
theorem strict_power_monotonic : FormulaProves
    ((pow2 (.var 1) (.var 2)).imp ((pow2 (.var 0) (.var 6)).imp
      ((less (.var 1) (.var 0)).imp (less (.var 2) (.var 6))))) := by
  let A := pow2 (.var 1) (.var 2)
  let B := pow2 (.var 0) (.var 6)
  let L := less (.var 1) (.var 0)
  let Γ := [L,B,A]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have ha : FOL.Context Peano.Axiom Γ A := .hypothesis (by simp [Γ])
  have hb : FOL.Context Peano.Axiom Γ B := .hypothesis (by simp [Γ])
  have hl : FOL.Context Peano.Axiom Γ L := .head _ _
  have hd : FOL.Context Peano.Axiom Γ
      (divides (add (.var 2) (.var 2)) (.var 6)) :=
    .mp (.mp (.mp (.closed PeanoPowerDivisibilityClosed.body_proved) ha) hb) hl
  have hu : FOL.Context Peano.Axiom Γ (less zero (.var 2)) :=
    .mp (.closed (PeanoPowerSingleton.power_positive (.var 1) (.var 2))) ha
  have hp : FOL.Context Peano.Axiom Γ (less zero (.var 6)) :=
    .mp (.closed (PeanoPowerSingleton.power_positive (.var 0) (.var 6))) hb
  exact .mp (.mp (.mp (.closed strict_from_doubled_divisor) hu) hp) hd

/-- Weak order of the indices implies weak order of the literal powers.
The weak comparisons are expressed as strict comparisons with successor. -/
theorem weak_power_monotonic : FormulaProves
    ((pow2 (.var 1) (.var 2)).imp ((pow2 (.var 0) (.var 6)).imp
      ((less (.var 1) (succ (.var 0))).imp (less (.var 2) (succ (.var 6)))))) := by
  let A := pow2 (.var 1) (.var 2)
  let B := pow2 (.var 0) (.var 6)
  let L := less (.var 1) (succ (.var 0))
  let E := (.var 1 : Peano.Term).equal (.var 0)
  let S := less (.var 1) (.var 0)
  let T := less (.var 2) (succ (.var 6))
  let Γ := [L,B,A]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have ha : FOL.Context Peano.Axiom Γ A := .hypothesis (by simp [Γ])
  have hb : FOL.Context Peano.Axiom Γ B := .hypothesis (by simp [Γ])
  have hl : FOL.Context Peano.Axiom Γ L := .head _ _
  have hE : FOL.Context Peano.Axiom Γ (E.imp T) := by
    apply FOL.Context.deduction
    exact .mp (.mp (.mp (.closed (equal_index_le (.var 1) (.var 0) (.var 2) (.var 6)))
      (FOL.Context.head _ _)) (.under ha E)) (.under hb E)
  have hS : FOL.Context Peano.Axiom Γ (S.imp T) := by
    apply FOL.Context.deduction
    have hstrict : FOL.Context Peano.Axiom (S :: Γ) (less (.var 2) (.var 6)) :=
      .mp (.mp (.mp (.closed strict_power_monotonic) (.under ha S)) (.under hb S)) (.head _ _)
    exact .mp (.mp (.closed (PeanoOrderTransitive.less_transitive_all
      (.var 2) (.var 6) (succ (.var 6)))) hstrict)
      (.closed (PeanoPowerTransition.self_less_succ (.var 6)))
  have hcases : FOL.Context Peano.Axiom Γ (E ⊔ S) :=
    .mp (.closed (PeanoCommonMultiple.BoundSplit.less_successor_cases (.var 1) (.var 0))) hl
  exact or_elim hcases hE hS

end PASoundness.PeanoPowerMonotonic

#print axioms PASoundness.PeanoPowerMonotonic.equal_index_le
#print axioms PASoundness.PeanoPowerMonotonic.strict_from_doubled_divisor
#print axioms PASoundness.PeanoPowerMonotonic.strict_power_monotonic
#print axioms PASoundness.PeanoPowerMonotonic.weak_power_monotonic
