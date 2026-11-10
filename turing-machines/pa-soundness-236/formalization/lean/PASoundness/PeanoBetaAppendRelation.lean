import PASoundness.PeanoBetaCRTAlignment
import PASoundness.PeanoBetaExistence

/-! The desired rows for appending a value to an existing beta-coded trace.
This file establishes only the availability of these desired rows; it does not
construct their common beta code or establish power-trace totality. -/
namespace PASoundness.PeanoBetaAppendRelation
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

/-- Old code 4, old parameter 5, length 0, terminal value 6, and row 2/3. -/
def appendRelation : Peano.Formula :=
  (less (.var 2) (succ (.var 0)) ⊓ beta (.var 4) (.var 5) (.var 2) (.var 3)) ⊔
  (((.var 2 : Peano.Term).equal (succ (.var 0))) ⊓
    ((.var 3 : Peano.Term).equal (add (.var 6) (.var 6))))

theorem append_names_safe : PeanoBetaCRTAlignment.NamesSafe appendRelation := by
  have hf : appendRelation.freeVarFinset = {0,2,3,4,5,6} := by decide
  intro x hx
  rw [hf] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

private theorem beta_exists_syntax :
    PeanoBetaExistence.betaExists (.var 4) (.var 5) (.var 2) =
      FOL.existsAt 3 (beta (.var 4) (.var 5) (.var 2) (.var 3)) := by
  let σ : Nat → Peano.Term := fun x => if x = 0 then .var 4 else if x = 1 then .var 5 else if x = 2 then .var 2 else if x = 3 then .var 3 else zero
  have he : PeanoBetaExistence.betaExists (.var 4) (.var 5) (.var 2) =
      (FOL.existsAt 3 (beta (.var 0) (.var 1) (.var 2) (.var 3))).subst σ := by
    unfold PeanoBetaExistence.betaExists PeanoBetaExistence.betaExistsTemplate
    apply SyntaxTransport.formula_subst_agree
    intro x hx
    have hv : (FOL.existsAt 3 (beta (.var 0) (.var 1) (.var 2) (.var 3))).freeVarFinset = {0,1,2} := by decide
    rw [hv] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> rfl
  rw [he, PeanoBetaCRTAlignment.arbitrary_subst_exists_at σ 3 (by rfl) (by
    intro x hx
    simp only [σ]
    split_ifs <;> simp_all [Peano.zero, FirstOrder.Language.Term.varFinset])]
  simp [beta_subst, σ, FirstOrder.Language.Term.subst]

private theorem old_case : FormulaProves
    ((less (.var 2) (succ (.var 0))).imp (FOL.existsAt 3 appendRelation)) := by
  let L := less (.var 2) (succ (.var 0))
  let B := beta (.var 4) (.var 5) (.var 2) (.var 3)
  let Q := ((.var 2 : Peano.Term).equal (succ (.var 0))) ⊓
    ((.var 3 : Peano.Term).equal (add (.var 6) (.var 6)))
  let T := FOL.existsAt 3 appendRelation
  have hb : FormulaProves (B.imp (L.imp T)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have hL : FOL.Context Peano.Axiom [L,B] L := FOL.Context.head _ _
    have hB : FOL.Context Peano.Axiom [L,B] B := FOL.Context.under (FOL.Context.head [] B) L
    have hp : FOL.Context Peano.Axiom [L,B] (L ⊓ B) := FOL.Context.conjunctionIntro hL hB
    have hu : FOL.Context Peano.Axiom [L,B] ((L ⊓ B) ⊔ Q) := by
      apply FOL.Context.deduction
      exact FOL.Context.explode Q (.mp (FOL.Context.head _ _) (FOL.Context.under hp _))
    have hi := FOL.Derivation.existsIntro (A := Peano.Axiom) appendRelation 3 (.var 3)
    exact .mp (.closed (by simpa only [SyntaxTransport.substAt_self] using hi)) (by simpa [appendRelation,L,B,Q] using hu)
  have hf : 3 ∉ (L.imp T).freeVarFinset := by decide
  have he := PeanoBitPositionReduction.exists_elim 3 hf hb
  have hx : FormulaProves (FOL.existsAt 3 B) := by
    simpa only [B, beta_exists_syntax] using (PeanoBetaExistence.beta_exists (.var 4) (.var 5) (.var 2))
  exact .mp he hx

private theorem subst_not (φ : Peano.Formula) (σ : Nat → Peano.Term) :
    φ.not.subst σ = (φ.subst σ).not := by
  simp [FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.mapTermRel]
  rfl
private theorem subst_and (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ ⊓ ψ).subst σ = (φ.subst σ) ⊓ (ψ.subst σ) := by
  change (φ.imp ψ.not).not.subst σ = ((φ.subst σ).imp (ψ.subst σ).not).not
  rw [subst_not, show (φ.imp ψ.not).subst σ = (φ.subst σ).imp (ψ.not.subst σ) from rfl, subst_not]
private theorem subst_or (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ ⊔ ψ).subst σ = (φ.subst σ) ⊔ (ψ.subst σ) := by
  change (φ.not.imp ψ).subst σ = ((φ.subst σ).not.imp (ψ.subst σ))
  rw [show (φ.not.imp ψ).subst σ = (φ.not.subst σ).imp (ψ.subst σ) from rfl, subst_not]

private theorem boundary_case : FormulaProves
    (((.var 2 : Peano.Term).equal (succ (.var 0))).imp
      (FOL.existsAt 3 appendRelation)) := by
  let E : Peano.Formula := (.var 2 : Peano.Term).equal (succ (.var 0))
  let t := add (.var 6) (.var 6)
  let P := less (.var 2) (succ (.var 0)) ⊓ beta (.var 4) (.var 5) (.var 2) t
  let Q := E ⊓ t.equal t
  have hsubst : FOL.substAt appendRelation 3 t = P ⊔ Q := by
    simp [FOL.substAt, appendRelation, P, Q, E, t, subst_or, subst_and, beta_subst,
      less_subst, FOL.equality_subst, add_subst, succ_subst, FirstOrder.Language.Term.subst]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have hE : FOL.Context Peano.Axiom [E] E := FOL.Context.head [] _
  have hq : FOL.Context Peano.Axiom [E] Q :=
    FOL.Context.conjunctionIntro hE (.closed (.logical (.eqRefl t)))
  have hu : FOL.Context Peano.Axiom [E] (P ⊔ Q) := FOL.Context.lift hq P.not
  have hi := FOL.Derivation.existsIntro (A := Peano.Axiom) appendRelation 3 t
  exact .mp (.closed (by rw [hsubst] at hi; exact hi)) hu

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

/-- PA supplies a desired row at every index below S(S n). Existing rows
use beta division; the final index uses the explicit value p+p. This does
not assert a common beta code for the resulting rows. -/
theorem append_rows_total : FormulaProves (FOL.allAt 2
    ((less (.var 2) (succ (succ (.var 0)))).imp (FOL.existsAt 3 appendRelation))) := by
  apply FOL.Derivation.generalize
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have hc := FOL.Context.mp
    (.closed (PeanoCommonMultiple.BoundSplit.less_successor_cases (.var 2) (succ (.var 0))))
    (FOL.Context.head [] (less (.var 2) (succ (succ (.var 0)))))
  exact or_elim hc (.closed boundary_case) (.closed old_case)


end PASoundness.PeanoBetaAppendRelation
