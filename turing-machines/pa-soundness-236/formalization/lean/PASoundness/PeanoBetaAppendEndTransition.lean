import PASoundness.PeanoBetaAppendPreserve
import PASoundness.PeanoBetaAppendBoundary
import PASoundness.PeanoBetaCRTPrefixSubst

/-! PA endpoint doubling transfer from supplied append-recoding rows. -/
namespace PASoundness.PeanoBetaAppendEndTransition
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoBetaAppendRelation

/-- A supplied recoding row with free index name 2. -/
def row : Peano.Formula := FOL.existsAt 3
  (appendRelation ⊓ beta (.var 9) (.var 1) (.var 2) (.var 3))
/-- Capture-safe instantiation of the recoding row at the old endpoint n. -/
def endpointRow : Peano.Formula := FOL.substAt row 2 (.var 0)
/-- Capture-safe instantiation of the recoding row at the appended index S n. -/
def appendedRow : Peano.Formula := FOL.substAt row 2 (succ (.var 0))

private theorem subst_imp (φ ψ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    FOL.substAt (φ.imp ψ) x t = (FOL.substAt φ x t).imp (FOL.substAt ψ x t) := rfl

private theorem endpoint_preserved : FormulaProves
    (endpointRow.imp ((beta (.var 4) (.var 5) (.var 0) (.var 6)).imp
      (beta (.var 9) (.var 1) (.var 0) (.var 6)))) := by
  let F := row.imp ((less (.var 2) (succ (.var 0))).imp
    ((beta (.var 4) (.var 5) (.var 2) (.var 20)).imp
      (beta (.var 9) (.var 1) (.var 2) (.var 20))))
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim F 2 (.var 0)))
    (.generalize 2 PeanoBetaAppendPreserve.old_row_preserved)
  dsimp only [F] at h
  rw [subst_imp, subst_imp, subst_imp] at h
  have h' : FormulaProves (endpointRow.imp ((less (.var 0) (succ (.var 0))).imp
    ((beta (.var 4) (.var 5) (.var 0) (.var 20)).imp
      (beta (.var 9) (.var 1) (.var 0) (.var 20))))) := by
    simpa [endpointRow, FOL.substAt, less_subst, succ_subst, beta_subst,
      FirstOrder.Language.Term.subst] using h
  let G := endpointRow.imp ((less (.var 0) (succ (.var 0))).imp
    ((beta (.var 4) (.var 5) (.var 0) (.var 20)).imp
      (beta (.var 9) (.var 1) (.var 0) (.var 20))))
  have h₂ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim G 20 (.var 6)))
    (.generalize 20 h')
  have hf : 20 ∉ endpointRow.freeVarFinset := by decide
  have hfix := PeanoBetaCRTPrefixSubst.Syntax.substAt_of_fresh endpointRow 20 (.var 6) hf
  dsimp only [G] at h₂
  rw [subst_imp, subst_imp, subst_imp, hfix] at h₂
  have h₃ : FormulaProves (endpointRow.imp ((less (.var 0) (succ (.var 0))).imp
    ((beta (.var 4) (.var 5) (.var 0) (.var 6)).imp
      (beta (.var 9) (.var 1) (.var 0) (.var 6))))) := by
    simpa [FOL.substAt, less_subst, succ_subst, beta_subst,
      FirstOrder.Language.Term.subst] using h₂
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  exact .mp (.mp (.mp (.closed h₃) (FOL.Context.under (FOL.Context.head [] endpointRow) _))
    (.closed (PeanoPowerTransition.self_less_succ (.var 0)))) (FOL.Context.head _ _)

private theorem appended_boundary : FormulaProves
    (appendedRow.imp (beta (.var 9) (.var 1) (succ (.var 0)) (add (.var 6) (.var 6)))) := by
  let F := row.imp (((.var 2 : Peano.Term).equal (succ (.var 0))).imp
    (beta (.var 9) (.var 1) (.var 2) (add (.var 6) (.var 6))))
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim F 2 (succ (.var 0))))
    (.generalize 2 PeanoBetaAppendBoundary.boundary_row)
  dsimp only [F] at h
  rw [subst_imp, subst_imp] at h
  have h' : FormulaProves (appendedRow.imp
    (((succ (.var 0)).equal (succ (.var 0))).imp
      (beta (.var 9) (.var 1) (succ (.var 0)) (add (.var 6) (.var 6))))) := by
    simpa [appendedRow, FOL.substAt, FOL.equality_subst, beta_subst, succ_subst,
      add_subst, FirstOrder.Language.Term.subst] using h
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  exact .mp (.mp (.closed h') (FOL.Context.head [] _))
    (.closed (.logical (.eqRefl (succ (.var 0)))))

/-- From supplied recoding rows at n and S n and the old endpoint β(B,C,n,p),
PA derives the new endpoint and its appended doubling row. Names are n=0,
new parameter=1, old B=4, old C=5, p=6, new B=9; witness 3 is bound. -/
theorem endpoint_doubling : FormulaProves
    (endpointRow.imp (appendedRow.imp
      ((beta (.var 4) (.var 5) (.var 0) (.var 6)).imp
        ((beta (.var 9) (.var 1) (.var 0) (.var 6)) ⊓
          ((beta (.var 9) (.var 1) (succ (.var 0)) (add (.var 6) (.var 6))) ⊓
            ((add (.var 6) (.var 6)).equal (add (.var 6) (.var 6)))))))) := by
  let E := beta (.var 4) (.var 5) (.var 0) (.var 6)
  let Γ := [E, appendedRow, endpointRow]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have he : FOL.Context Peano.Axiom Γ E := FOL.Context.head _ _
  have hr : FOL.Context Peano.Axiom Γ endpointRow := .hypothesis (by simp [Γ])
  have ha : FOL.Context Peano.Axiom Γ appendedRow := .hypothesis (by simp [Γ])
  exact FOL.Context.conjunctionIntro (.mp (.mp (.closed endpoint_preserved) hr) he)
    (FOL.Context.conjunctionIntro (.mp (.closed appended_boundary) ha)
      (.closed (.logical (.eqRefl (add (.var 6) (.var 6))))))

end PASoundness.PeanoBetaAppendEndTransition

#print axioms PASoundness.PeanoBetaAppendEndTransition.endpoint_doubling
