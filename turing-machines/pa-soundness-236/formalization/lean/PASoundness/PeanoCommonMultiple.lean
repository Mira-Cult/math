import PASoundness.PeanoDivisibility
import PASoundness.PeanoDivisionSuccessor
import PASoundness.PeanoPowerTransition
import PASoundness.PeanoEmptyBitSet

/-! For arbitrary arithmetic terms N and R, the object-level PA calculus
proves the existence of C > R divisible by S j for every j < N. The proof
uses induction with base C = S R and successor witness C * S N. The standard
meaning of the capture-safe formula is proved separately. -/

/-! A strict PA bound is preserved by multiplication by a successor. -/
namespace PASoundness.PeanoCommonMultiple.ScaledBound
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoAdditionAssociative PeanoMultiplyQuotientStep
open CompactArithmetic

/-- For arbitrary arithmetic terms, PA derives that `R < C` implies
`R < C*(S N)`. No multiplication positivity premise is assumed. -/
theorem less_mul_succ (R C N : Peano.Term) :
    FormulaProves ((less R C).imp (less R (mul C (succ N)))) := by
  have he : FormulaProves ((add C (mul C N)).equal (mul C (succ N))) :=
    FOL.Derivation.eqTrans (add_comm C (mul C N))
      (FOL.Derivation.eqSymm (.axiom (.mul_succ C N)))
  exact FOL.Derivation.compose (PeanoQuotientGap.less_add_right R C (mul C N))
    (.mp (less_right_congr R (add C (mul C N)) (mul C (succ N))) he)

end PASoundness.PeanoCommonMultiple.ScaledBound


/-! A PA derivation splitting a strict successor bound. -/
namespace PASoundness.PeanoCommonMultiple.BoundSplit
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

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

/-- A strict successor bound places the first term at or below the predecessor.
The result uses the literal order and equality formulas of the PA calculus. -/
theorem less_successor_cases (j n : Peano.Term) :
    FormulaProves ((less j (succ n)).imp ((j.equal n) ⊔ less j n)) := by
  let L := less j (succ n)
  let G := less n j
  let T := (j.equal n) ⊔ less j n
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have hL : FOL.Context Peano.Axiom [L] L := FOL.Context.head [] L
  have hT : FOL.Context Peano.Axiom [L] (T.imp T) := by
    apply FOL.Context.deduction
    exact FOL.Context.head [L] T
  have hG : FOL.Context Peano.Axiom [L] (G.imp T) := by
    apply FOL.Context.deduction
    have hbad : FOL.Context Peano.Axiom [G, L] L.not :=
      .mp (.closed (PeanoDivisionSuccessor.no_gap_all n j)) (FOL.Context.head [L] G)
    exact FOL.Context.explode T (.mp hbad (FOL.Context.under hL G))
  exact or_elim (.closed (PeanoOrderTotality.trichotomy_all j n)) hT hG

end PASoundness.PeanoCommonMultiple.BoundSplit


/-! Divisibility transport and the newly added factor in a PA common multiple. -/
namespace PASoundness.PeanoCommonMultiple.DivisibilityBoundary
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic PeanoDivisibility

private theorem divides_subst (k d : Peano.Term) (σ : Nat → Peano.Term) :
    (divides k d).subst σ = divides (k.subst σ) (d.subst σ) := by
  unfold divides
  rw [SyntaxTransport.formula_subst_comp]
  congr 1
  funext y
  by_cases h0 : y = 0 <;> by_cases h1 : y = 1 <;> simp [h0, h1]

/-- Transport a divisor equality inside the literal PA divisibility formula. -/
theorem divisor_congr (a b d : Peano.Term) :
    FormulaProves ((a.equal b).imp ((divides a d).imp (divides b d))) := by
  obtain ⟨i, hi⟩ := FOL.fresh_for_term d
  let φ : Peano.Formula := divides (.var i) d
  have h₀ : FOL.substAt φ i a = divides a d := by
    simp only [FOL.substAt, φ, divides_subst, FirstOrder.Language.Term.subst,
      ↓reduceIte, FOL.term_subst_fresh d i a hi]
  have h₁ : FOL.substAt φ i b = divides b d := by
    simp only [FOL.substAt, φ, divides_subst, FirstOrder.Language.Term.subst,
      ↓reduceIte, FOL.term_subst_fresh d i b hi]
  have h := FOL.Derivation.logical (Axiom := Peano.Axiom)
    (FOL.LogicalAxiom.eqSubst φ i a b)
  rw [h₀, h₁] at h
  exact h

/-- Transport a dividend equality inside the literal PA divisibility formula. -/
theorem dividend_congr (k a b : Peano.Term) :
    FormulaProves ((a.equal b).imp ((divides k a).imp (divides k b))) := by
  obtain ⟨i, hi⟩ := FOL.fresh_for_term k
  let φ : Peano.Formula := divides k (.var i)
  have h₀ : FOL.substAt φ i a = divides k a := by
    simp only [FOL.substAt, φ, divides_subst, FirstOrder.Language.Term.subst,
      ↓reduceIte, FOL.term_subst_fresh k i a hi]
  have h₁ : FOL.substAt φ i b = divides k b := by
    simp only [FOL.substAt, φ, divides_subst, FirstOrder.Language.Term.subst,
      ↓reduceIte, FOL.term_subst_fresh k i b hi]
  have h := FOL.Derivation.logical (Axiom := Peano.Axiom)
    (FOL.LogicalAxiom.eqSubst φ i a b)
  rw [h₀, h₁] at h
  exact h

/-- Any factor divides the product, using the explicit quotient produced by
`divides_self` and `divides_mul`. -/
theorem factor_divides_product (k c : Peano.Term) :
    FormulaProves (divides k (mul c k)) := by
  have h : FormulaProves (divides k (mul k c)) :=
    .mp (divides_mul k k c) (divides_self k)
  have hc : FormulaProves ((mul k c).equal (mul c k)) :=
    PeanoBetaProductIncrement.mul_comm k c
  exact .mp (.mp (dividend_congr k (mul k c) (mul c k)) hc) h

/-- When `j=N`, the new factor `S N` is divisible by the required `S j`. -/
theorem boundary_divides_product (j n c : Peano.Term) :
    FormulaProves ((j.equal n).imp (divides (succ j) (mul c (succ n)))) := by
  let E := j.equal n
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have he : FOL.Context Peano.Axiom [E] ((succ n).equal (succ j)) :=
    FOL.Context.eqSymm (.mp (.closed (PeanoOrderIrreflexive.succ_congr j n))
      (FOL.Context.head [] E))
  exact .mp (.mp (.closed (divisor_congr (succ n) (succ j) (mul c (succ n)))) he)
    (.closed (factor_divides_product (succ n) c))

end PASoundness.PeanoCommonMultiple.DivisibilityBoundary

namespace PASoundness.PeanoCommonMultiple.Step
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoDivisibility

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

def body (n r c : Peano.Term) : Peano.Formula :=
  (less r c) ⊓ FOL.allAt 3 ((less (.var 3) n).imp (divides (succ (.var 3)) c))

def initialBody := body (.var 0) (.var 1) (.var 2)
def nextBody := body (succ (.var 0)) (.var 1) (mul (.var 2) (succ (.var 0)))

def splitFormula : Peano.Formula :=
  (less (.var 3) (succ (.var 0))).imp
    (((.var 3 : Peano.Term).equal (.var 0)) ⊔ less (.var 3) (.var 0))
def boundaryFormula : Peano.Formula :=
  ((.var 3 : Peano.Term).equal (.var 0)).imp
    (divides (succ (.var 3)) (mul (.var 2) (succ (.var 0))))
def boundFormula : Peano.Formula :=
  (less (.var 1) (.var 2)).imp (less (.var 1) (mul (.var 2) (succ (.var 0))))

/-- The bounded-uniform successor step from three explicit PA derivations:
new-index split, boundary divisor, and preservation of the lower bound. -/
theorem body_step_conditional (hsplit : FormulaProves splitFormula)
    (hboundary : FormulaProves boundaryFormula) (hbound : FormulaProves boundFormula) :
    FormulaProves (initialBody.imp nextBody) := by
  let L := less (.var 3) (.var 0)
  let L' := less (.var 3) (succ (.var 0))
  let E := (.var 3 : Peano.Term).equal (.var 0)
  let D := divides (succ (.var 3)) (.var 2)
  let D' := divides (succ (.var 3)) (mul (.var 2) (succ (.var 0)))
  let old : Peano.Formula := FOL.allAt 3 (L.imp D)
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have hb : FOL.Context Peano.Axiom [initialBody] initialBody := FOL.Context.head [] initialBody
  have hr : FOL.Context Peano.Axiom [initialBody] (less (.var 1) (.var 2)) :=
    FOL.Context.conjunctionLeft hb
  have ho : FOL.Context Peano.Axiom [initialBody] old := FOL.Context.conjunctionRight hb
  have hnewbound : FOL.Context Peano.Axiom [initialBody]
      (less (.var 1) (mul (.var 2) (succ (.var 0)))) := .mp (.closed hbound) hr
  have hnewall : FOL.Context Peano.Axiom [initialBody] (FOL.allAt 3 (L'.imp D')) := by
    apply FOL.Context.generalize 3
    · intro ψ hψ
      have he : ψ = initialBody := by simpa only [List.mem_singleton] using hψ
      subst ψ
      decide
    · apply FOL.Context.deduction
      let Γ := [L', initialBody]
      have hsmall : FOL.Context Peano.Axiom Γ (L'.imp (E ⊔ L)) := .closed hsplit
      have hcases : FOL.Context Peano.Axiom Γ (E ⊔ L) :=
        .mp hsmall (FOL.Context.head [initialBody] L')
      have he : FOL.Context Peano.Axiom Γ (E.imp D') := .closed hboundary
      have hl : FOL.Context Peano.Axiom Γ (L.imp D') := by
        apply FOL.Context.deduction
        have h_old : FOL.Context Peano.Axiom (L :: Γ) old :=
          FOL.Context.under (FOL.Context.under ho L') L
        have h_instance : FOL.Context Peano.Axiom (L :: Γ) (L.imp D) :=
          FOL.Context.allSelf h_old
        have h_div : FOL.Context Peano.Axiom (L :: Γ) D :=
          .mp h_instance (FOL.Context.head Γ L)
        exact .mp (.closed (divides_mul (succ (.var 3)) (.var 2) (succ (.var 0)))) h_div
      exact or_elim hcases he hl
  exact FOL.Context.conjunctionIntro hnewbound hnewall

end PASoundness.PeanoCommonMultiple.Step

namespace PASoundness.PeanoCommonMultiple.Step
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoDivisibility

/-- Complete bounded-uniform successor step: the input common-divisor
invariant for N,C implies the invariant for S N,C*(S N). -/
theorem body_step : Peano.FormulaProves (initialBody.imp nextBody) :=
  body_step_conditional
    (PeanoCommonMultiple.BoundSplit.less_successor_cases (.var 3) (.var 0))
    (PeanoCommonMultiple.DivisibilityBoundary.boundary_divides_product (.var 3) (.var 0) (.var 2))
    (PeanoCommonMultiple.ScaledBound.less_mul_succ (.var 1) (.var 2) (.var 0))


end PASoundness.PeanoCommonMultiple.Step

namespace PASoundness.PeanoCommonMultiple
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic PeanoDivisibility

/-- A fixed-name matrix for the common-multiple induction. Names 2 and 3 are
reserved for the candidate and bounded divisor; arbitrary-terms applications
must instead use `commonMultiple`. -/
def body (n r c : Peano.Term) : Peano.Formula :=
  (less r c) ⊓ FOL.allAt 3 ((less (.var 3) n).imp (divides (succ (.var 3)) c))

def common (n r : Peano.Term) : Peano.Formula :=
  FOL.existsAt 2 (body n r (.var 2))

/-- The two free names are the bound on the divisor index and the lower bound. -/
def commonTemplate : Peano.Formula := common (.var 0) (.var 1)

/-- Capture-safe substitution into the fixed-name induction template. -/
def commonMultiple (n r : Peano.Term) : Peano.Formula :=
  commonTemplate.subst (fun y => if y = 0 then n else if y = 1 then r else zero)

private theorem base_body : FormulaProves (body zero (.var 1) (succ (.var 1))) := by
  have hall : FormulaProves (FOL.allAt 3
      ((less (.var 3) zero).imp (divides (succ (.var 3)) (succ (.var 1))))) := by
    apply FOL.Derivation.generalize 3
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    exact FOL.Context.explode _
      (.mp (.closed (PeanoEmptyBitSet.no_less_zero (.var 3))) (FOL.Context.head [] _))
  apply FOL.Context.closeEmpty
  exact FOL.Context.conjunctionIntro (.closed (PeanoPowerTransition.self_less_succ (.var 1))) (.closed hall)

private theorem base_subst : FOL.substAt (body zero (.var 1) (.var 2)) 2 (succ (.var 1)) =
    body zero (.var 1) (succ (.var 1)) := by
  simp [FOL.substAt, body, divides, dividesTemplate, FOL.existsAt, FOL.allAt,
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

theorem common_zero : FormulaProves (common zero (.var 1)) := by
  have hi := FOL.Derivation.existsIntro (A := Peano.Axiom) (body zero (.var 1) (.var 2)) 2 (succ (.var 1))
  rw [base_subst] at hi
  exact .mp hi base_body


/-- Standard meaning of the formula; this semantic statement is separate
from any PA derivation of common-multiple existence. -/
theorem commonMultiple_realize (n r : Peano.Term) (ρ : Nat → Nat) :
    (commonMultiple n r).Realize ρ ↔
      ∃ c : Nat, r.realize ρ < c ∧
        ∀ j : Nat, j < n.realize ρ → ∃ q : Nat, c = q * (j + 1) := by
  classical
  simp [commonMultiple, commonTemplate, common, body, FOL.existsAt, FOL.realize_allAt,
    FOL.realize_subst, Classical.not_forall, Peano.realize_succ, divides_realize]

private theorem commonMultiple_subst (n r : Peano.Term) (σ : Nat → Peano.Term) :
    (commonMultiple n r).subst σ = commonMultiple (n.subst σ) (r.subst σ) := by
  unfold commonMultiple
  rw [SyntaxTransport.formula_subst_comp]
  congr 1
  funext y
  by_cases h0 : y = 0 <;> by_cases h1 : y = 1 <;> simp [h0, h1]

private theorem template_freeVars : commonTemplate.freeVarFinset = {0,1} := by decide

private theorem template_as_commonMultiple : commonMultiple (.var 0) (.var 1) = commonTemplate := by
  unfold commonMultiple
  calc
    commonTemplate.subst (fun y => if y = 0 then .var 0 else if y = 1 then .var 1 else zero) =
        commonTemplate.subst Term.var := by
      apply SyntaxTransport.formula_subst_agree
      intro y hy
      simp only [template_freeVars, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> rfl
    _ = commonTemplate := SyntaxTransport.formula_subst_var _

private def nextCommon : Peano.Formula := common (succ (.var 0)) (.var 1)

private theorem next_body_subst :
    FOL.substAt (body (succ (.var 0)) (.var 1) (.var 2)) 2
      (mul (.var 2) (succ (.var 0))) =
    body (succ (.var 0)) (.var 1) (mul (.var 2) (succ (.var 0))) := by
  simp [FOL.substAt, body, divides, dividesTemplate, FOL.existsAt, FOL.allAt,
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

/-- Package the concrete product witness and eliminate the old candidate. -/
private theorem common_step_of_body
    (hbody : FormulaProves ((body (.var 0) (.var 1) (.var 2)).imp
      (body (succ (.var 0)) (.var 1) (mul (.var 2) (succ (.var 0)))))) :
    FormulaProves (commonTemplate.imp nextCommon) := by
  have hi := FOL.Derivation.existsIntro (A := Peano.Axiom)
    (body (succ (.var 0)) (.var 1) (.var 2)) 2 (mul (.var 2) (succ (.var 0)))
  rw [next_body_subst] at hi
  have hp : FormulaProves ((body (.var 0) (.var 1) (.var 2)).imp nextCommon) :=
    FOL.Derivation.compose hbody hi
  have hfresh : 2 ∉ nextCommon.freeVarFinset := by decide
  have h := PeanoBitPositionReduction.exists_elim 2 hfresh hp
  simpa only [commonTemplate, common] using h

private theorem template_zero : FOL.substAt commonTemplate 0 zero = common zero (.var 1) := by
  simp [FOL.substAt, commonTemplate, common, body, divides, dividesTemplate, FOL.existsAt, FOL.allAt,
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

private theorem template_succ : FOL.substAt commonTemplate 0 (succ (.var 0)) = nextCommon := by
  simp [FOL.substAt, nextCommon, commonTemplate, common, body, divides, dividesTemplate, FOL.existsAt, FOL.allAt,
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

private theorem variables_of_body_step
    (hbody : FormulaProves ((body (.var 0) (.var 1) (.var 2)).imp
      (body (succ (.var 0)) (.var 1) (mul (.var 2) (succ (.var 0)))))) :
    FormulaProves commonTemplate := by
  have hb : FormulaProves (FOL.substAt commonTemplate 0 zero) := by
    rw [template_zero]
    exact common_zero
  have hs : FormulaProves (commonTemplate.imp (FOL.substAt commonTemplate 0 (succ (.var 0)))) := by
    rw [template_succ]
    exact common_step_of_body hbody
  have hall : FormulaProves (FOL.allAt 0 commonTemplate) :=
    .mp (.mp (.axiom (.induction commonTemplate 0)) hb) (.generalize 0 hs)
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim commonTemplate 0 (.var 0))) hall
  simpa only [SyntaxTransport.substAt_self] using h

private theorem specialize (n r : Peano.Term) (name : Nat) (t : Peano.Term)
    (h : FormulaProves (commonMultiple n r)) : FormulaProves (commonMultiple
      (n.subst (fun y => if y = name then t else .var y))
      (r.subst (fun y => if y = name then t else .var y))) := by
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (commonMultiple n r) name t))
    (.generalize name h)
  simpa only [FOL.substAt, commonMultiple_subst] using h₁

private theorem from_variables
    (hvar : FormulaProves (commonMultiple (.var 0) (.var 1))) (n r : Peano.Term) :
    FormulaProves (commonMultiple n r) := by
  let support := n.varFinset ∪ r.varFinset
  let k := support.sup id + 2
  have hk : 2 ≤ k := by dsimp [k]; omega
  have fresh (j : Nat) (hj : k ≤ j) : j ∉ support := by
    intro h
    have hle : j ≤ support.sup id := Finset.le_sup (f := id) h
    dsimp [k] at hj
    omega
  have hn : k+1 ∉ n.varFinset := by
    intro h
    apply fresh (k+1) (by omega)
    simp [support, h]
  have h1 := specialize _ _ 0 (.var k) hvar
  have h1' : FormulaProves (commonMultiple (.var k) (.var 1)) := by
    simpa [FirstOrder.Language.Term.subst] using h1
  have h2 := specialize _ _ 1 (.var (k+1)) h1'
  have h2' : FormulaProves (commonMultiple (.var k) (.var (k+1))) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 1 by omega] using h2
  have h3 := specialize _ _ k n h2'
  have h3' : FormulaProves (commonMultiple n (.var (k+1))) := by
    simpa [FirstOrder.Language.Term.subst, show k+1 ≠ k by omega] using h3
  have h4 := specialize _ _ (k+1) r h3'
  simpa [FirstOrder.Language.Term.subst,
    FOL.term_subst_fresh n (k+1) r hn] using h4

/-- For arbitrary terms N,R, PA constructs a common multiple C above R of
all successors S j with j<N. No choice of a metatheoretic factorial or CRT
solution is assumed in this derivation. -/
theorem common_multiple_exists (n r : Peano.Term) : FormulaProves (commonMultiple n r) := by
  have hbody : FormulaProves ((body (.var 0) (.var 1) (.var 2)).imp
      (body (succ (.var 0)) (.var 1) (mul (.var 2) (succ (.var 0))))) := by
    simpa only [Step.initialBody, Step.nextBody, Step.body, body] using Step.body_step
  have hvar : FormulaProves (commonMultiple (.var 0) (.var 1)) := by
    rw [template_as_commonMultiple]
    exact variables_of_body_step hbody
  exact from_variables hvar n r

end PASoundness.PeanoCommonMultiple
