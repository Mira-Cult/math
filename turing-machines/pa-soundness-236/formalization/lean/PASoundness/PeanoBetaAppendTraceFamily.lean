import PASoundness.PeanoBetaAppendTransition
import PASoundness.PeanoBetaCRTInvariant

/-! Transfer of the old bounded doubling-transition family to an append code.
The boundary at n and the literal pow2 trace remain separate obligations. -/
namespace PASoundness.PeanoBetaAppendTraceFamily
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoBetaAppendTransition PeanoBetaAppendRelation PeanoBetaCRTInvariant

def oldBody : Peano.Formula :=
  (O (.var 2) (.var 20)) ⊓ ((O (succ (.var 2)) (.var 21)) ⊓
    ((.var 21 : Peano.Term).equal (add (.var 20) (.var 20))))

def newBody : Peano.Formula :=
  (N (.var 2) (.var 20)) ⊓ ((N (succ (.var 2)) (.var 21)) ⊓
    ((.var 21 : Peano.Term).equal (add (.var 20) (.var 20))))

def oldFamily : Peano.Formula := FOL.allAt 2
  ((less (.var 2) (.var 0)).imp (FOL.existsAt 20 (FOL.existsAt 21 oldBody)))

def newFamily : Peano.Formula := FOL.allAt 2
  ((less (.var 2) (.var 0)).imp (FOL.existsAt 20 (FOL.existsAt 21 newBody)))

def recodedRows : Peano.Formula := rowsAt appendRelation (succ (succ (.var 0))) 9

/-- For supplied rows at i and S i, transfer one existential doubling pair,
retaining its value witnesses under capture-safe existential binders. -/
theorem transition_exists : FormulaProves
    ((FOL.existsAt 20 (FOL.existsAt 21 oldBody)).imp
      (row.imp (nextRow.imp ((less (.var 2) (.var 0)).imp
        (FOL.existsAt 20 (FOL.existsAt 21 newBody)))))) := by
  let G := less (.var 2) (.var 0)
  let T := FOL.existsAt 20 (FOL.existsAt 21 newBody)
  let P := row.imp (nextRow.imp (G.imp T))
  have hb : FormulaProves (oldBody.imp P) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    let Γ := [G, nextRow, row, oldBody]
    have ho : FOL.Context Peano.Axiom Γ oldBody := .hypothesis (by simp [Γ])
    have hr : FOL.Context Peano.Axiom Γ row := .hypothesis (by simp [Γ])
    have hs : FOL.Context Peano.Axiom Γ nextRow := .hypothesis (by simp [Γ])
    have hg : FOL.Context Peano.Axiom Γ G := FOL.Context.head _ _
    have hn : FOL.Context Peano.Axiom Γ newBody :=
      .mp (.mp (.mp (.mp (.mp (.mp (.closed transition_preserved) hr) hs) hg)
        (FOL.Context.conjunctionLeft ho)) (FOL.Context.conjunctionLeft (FOL.Context.conjunctionRight ho)))
        (FOL.Context.conjunctionRight (FOL.Context.conjunctionRight ho))
    have h21 : FormulaProves (newBody.imp (FOL.existsAt 21 newBody)) := by
      simpa only [SyntaxTransport.substAt_self] using
        (FOL.Derivation.existsIntro (A := Peano.Axiom) newBody 21 (.var 21))
    have h20 : FormulaProves ((FOL.existsAt 21 newBody).imp T) := by
      simpa only [T, SyntaxTransport.substAt_self] using
        (FOL.Derivation.existsIntro (A := Peano.Axiom) (FOL.existsAt 21 newBody) 20 (.var 20))
    exact .mp (.closed h20) (.mp (.closed h21) hn)
  have hf21 : 21 ∉ P.freeVarFinset := by decide
  have he21 := PeanoBitPositionReduction.exists_elim 21 hf21 hb
  have hf20 : 20 ∉ P.freeVarFinset := by decide
  exact PeanoBitPositionReduction.exists_elim 20 hf20 he21

private theorem subst_and (φ ψ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    FOL.substAt (φ ⊓ ψ) x t = (FOL.substAt φ x t) ⊓ (FOL.substAt ψ x t) := rfl

/-- Both indices are within the supplied row family whenever i<n. -/
theorem row_instances : FormulaProves
    ((rowsAt appendRelation (succ (succ (.var 0))) 9).imp
      ((less (.var 2) (.var 0)).imp (row ⊓ nextRow))) := by
  let endIndex : Peano.Term := succ (succ (.var 0))
  let F := rowsAt appendRelation endIndex 9
  let G := less (.var 2) (.var 0)
  let A := less (.var 2) endIndex
  let B := less (succ (.var 2)) endIndex
  let body := A.imp row
  have hinst : FormulaProves (F.imp (B.imp nextRow)) := by
    have h := FOL.Derivation.logical (Axiom := Peano.Axiom)
      (FOL.LogicalAxiom.allElim body 2 (succ (.var 2)))
    have he : FOL.substAt row 2 (succ (.var 2)) = nextRow := by
      rw [row, PeanoBetaCRTPrefixSubst.Syntax.subst_succSelf_existsAt _ 2 3 (by decide), subst_and]
      simp [nextRow, successorRelation, N, FOL.substAt, beta_subst,
        FirstOrder.Language.Term.subst]
    change FormulaProves (F.imp (FOL.substAt body 2 (succ (.var 2)))) at h
    rw [show FOL.substAt body 2 (succ (.var 2)) =
      (FOL.substAt A 2 (succ (.var 2))).imp (FOL.substAt row 2 (succ (.var 2))) from rfl, he] at h
    simpa [A, B, endIndex, FOL.substAt, less_subst, succ_subst,
      FirstOrder.Language.Term.subst] using h
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let Γ := [G, F]
  have hg : FOL.Context Peano.Axiom Γ G := FOL.Context.head _ _
  have hf : FOL.Context Peano.Axiom Γ F := .hypothesis (by simp [Γ])
  have hmid : FOL.Context Peano.Axiom Γ (less (.var 2) (succ (.var 0))) :=
    .mp (.mp (.closed (PeanoOrderTransitive.less_transitive_all (.var 2) (.var 0) (succ (.var 0)))) hg)
      (.closed (PeanoPowerTransition.self_less_succ (.var 0)))
  have ha : FOL.Context Peano.Axiom Γ A :=
    .mp (.mp (.closed (PeanoOrderTransitive.less_transitive_all (.var 2) (succ (.var 0)) endIndex)) hmid)
      (.closed (PeanoPowerTransition.self_less_succ (succ (.var 0))))
  have hb0 : FOL.Context Peano.Axiom Γ (less (succ (.var 2)) (succ (.var 0))) :=
    .mp (.closed (PeanoOrderSuccessor.less_succ_iff (.var 2) (.var 0)).1) hg
  have hb : FOL.Context Peano.Axiom Γ B :=
    .mp (.mp (.closed (PeanoOrderTransitive.less_transitive_all (succ (.var 2)) (succ (.var 0)) endIndex)) hb0)
      (.closed (PeanoPowerTransition.self_less_succ (succ (.var 0))))
  have hself : FOL.Context Peano.Axiom Γ (A.imp row) := FOL.Context.allSelf hf
  exact FOL.Context.conjunctionIntro (.mp hself ha) (.mp (.mp (.closed hinst) hf) hb)

/-- Every old doubling transition below n is preserved by a supplied family
of append recoding rows. The witness names remain bound inside each family. -/
theorem family_preserved : FormulaProves
    (oldFamily.imp (recodedRows.imp newFamily)) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.generalize 2
  · intro ψ hψ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hψ
    rcases hψ with rfl | rfl <;> decide
  apply FOL.Context.deduction
  let G := less (.var 2) (.var 0)
  let Γ := [G, recodedRows, oldFamily]
  have hg : FOL.Context Peano.Axiom Γ G := FOL.Context.head _ _
  have hr : FOL.Context Peano.Axiom Γ recodedRows := .hypothesis (by simp [Γ])
  have ho : FOL.Context Peano.Axiom Γ oldFamily := .hypothesis (by simp [Γ])
  have hbody : FOL.Context Peano.Axiom Γ
      (G.imp (FOL.existsAt 20 (FOL.existsAt 21 oldBody))) := FOL.Context.allSelf ho
  have hp : FOL.Context Peano.Axiom Γ (row ⊓ nextRow) :=
    .mp (.mp (.closed row_instances) hr) hg
  exact .mp (.mp (.mp (.mp (.closed transition_exists) (.mp hbody hg))
    (FOL.Context.conjunctionLeft hp)) (FOL.Context.conjunctionRight hp)) hg


end PASoundness.PeanoBetaAppendTraceFamily

#print axioms PASoundness.PeanoBetaAppendTraceFamily.transition_exists
#print axioms PASoundness.PeanoBetaAppendTraceFamily.family_preserved
