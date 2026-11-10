import PASoundness.PeanoBetaAppendPreserve
import PASoundness.PeanoBetaCRTPrefixSubst
import PASoundness.PeanoBetaCRTAlpha

/-! PA transfer of an existing doubling pair to a supplied append recoding. -/
namespace PASoundness.PeanoBetaAppendTransition
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoBetaAppendRelation

def L := less (.var 2) (succ (.var 0))
def O (i r : Peano.Term) := beta (.var 4) (.var 5) i r
def N (i r : Peano.Term) := beta (.var 9) (.var 1) i r
def row := FOL.existsAt 3 (appendRelation ⊓ N (.var 2) (.var 3))
/-- Capture-safe instance of the append relation at successor index `S i`. -/
def successorRelation := FOL.substAt appendRelation 2 (succ (.var 2))
/-- The supplied recoding row at successor index, with witness name 3. -/
def nextRow := FOL.existsAt 3 (successorRelation ⊓ N (succ (.var 2)) (.var 3))

private theorem subst_imp (φ ψ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    FOL.substAt (φ.imp ψ) x t = (FOL.substAt φ x t).imp (FOL.substAt ψ x t) := rfl
private theorem subst_and (φ ψ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    FOL.substAt (φ ⊓ ψ) x t = (FOL.substAt φ x t) ⊓ (FOL.substAt ψ x t) := rfl

private theorem successor_preserved : FormulaProves
    (nextRow.imp ((less (succ (.var 2)) (succ (.var 0))).imp
      ((O (succ (.var 2)) (.var 20)).imp (N (succ (.var 2)) (.var 20))))) := by
  let F := row.imp (L.imp ((O (.var 2) (.var 20)).imp (N (.var 2) (.var 20))))
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim F 2 (succ (.var 2))))
    (.generalize 2 PeanoBetaAppendPreserve.old_row_preserved)
  have he : FOL.substAt row 2 (succ (.var 2)) = nextRow := by
    rw [row, PeanoBetaCRTPrefixSubst.Syntax.subst_succSelf_existsAt _ 2 3 (by decide), subst_and]
    simp [nextRow, successorRelation, N, FOL.substAt, beta_subst,
      FirstOrder.Language.Term.subst]
  dsimp only [F] at h
  rw [subst_imp, subst_imp, subst_imp, he] at h
  simpa [L, O, N, FOL.substAt, less_subst, succ_subst,
    beta_subst, FirstOrder.Language.Term.subst] using h

private theorem successor_preserved_21 : FormulaProves
    (nextRow.imp ((less (succ (.var 2)) (succ (.var 0))).imp
      ((O (succ (.var 2)) (.var 21)).imp (N (succ (.var 2)) (.var 21))))) := by
  let F := nextRow.imp ((less (succ (.var 2)) (succ (.var 0))).imp
    ((O (succ (.var 2)) (.var 20)).imp (N (succ (.var 2)) (.var 20))))
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim F 20 (.var 21)))
    (.generalize 20 successor_preserved)
  have hf : 20 ∉ nextRow.freeVarFinset := by decide
  have hn := PeanoBetaCRTPrefixSubst.Syntax.substAt_of_fresh nextRow 20 (.var 21) hf
  dsimp only [F] at h
  rw [subst_imp, subst_imp, subst_imp, hn] at h
  simpa [O, N, FOL.substAt, less_subst, succ_subst,
    beta_subst, FirstOrder.Language.Term.subst] using h

/-- From two supplied recoding rows and an old doubling pair at indices i and
S i, PA proves the same doubling pair for the new code. Names: old n=0,
index=2, old B=4, old C=5, new C=1, new B=9, row values r=20 and s=21;
3 is bound in each supplied recoding row. -/
theorem transition_preserved : FormulaProves
    (row.imp (nextRow.imp ((less (.var 2) (.var 0)).imp
      ((O (.var 2) (.var 20)).imp ((O (succ (.var 2)) (.var 21)).imp
        (((.var 21 : Peano.Term).equal (add (.var 20) (.var 20))).imp
          ((N (.var 2) (.var 20)) ⊓
            ((N (succ (.var 2)) (.var 21)) ⊓
              ((.var 21 : Peano.Term).equal (add (.var 20) (.var 20))))))))))) := by
  let H := (.var 21 : Peano.Term).equal (add (.var 20) (.var 20))
  let A := O (.var 2) (.var 20)
  let B := O (succ (.var 2)) (.var 21)
  let G := less (.var 2) (.var 0)
  let Γ := [H, B, A, G, nextRow, row]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hrow : FOL.Context Peano.Axiom Γ row := .hypothesis (by simp [Γ])
  have hnext : FOL.Context Peano.Axiom Γ nextRow := .hypothesis (by simp [Γ])
  have hg : FOL.Context Peano.Axiom Γ G := .hypothesis (by simp [Γ])
  have ha : FOL.Context Peano.Axiom Γ A := .hypothesis (by simp [Γ])
  have hb : FOL.Context Peano.Axiom Γ B := .hypothesis (by simp [Γ])
  have he : FOL.Context Peano.Axiom Γ H := FOL.Context.head _ _
  have hl : FOL.Context Peano.Axiom Γ L :=
    .mp (.mp (.closed (PeanoOrderTransitive.less_transitive_all (.var 2) (.var 0) (succ (.var 0)))) hg)
      (.closed (PeanoPowerTransition.self_less_succ (.var 0)))
  have hs : FOL.Context Peano.Axiom Γ (less (succ (.var 2)) (succ (.var 0))) :=
    .mp (.closed (PeanoOrderSuccessor.less_succ_iff (.var 2) (.var 0)).1) hg
  have hnew : FOL.Context Peano.Axiom Γ (N (.var 2) (.var 20)) :=
    .mp (.mp (.mp (.closed PeanoBetaAppendPreserve.old_row_preserved) hrow) hl) ha
  have hnewnext : FOL.Context Peano.Axiom Γ (N (succ (.var 2)) (.var 21)) :=
    .mp (.mp (.mp (.closed successor_preserved_21) hnext) hs) hb
  exact FOL.Context.conjunctionIntro hnew (FOL.Context.conjunctionIntro hnewnext he)

end PASoundness.PeanoBetaAppendTransition

#print axioms PASoundness.PeanoBetaAppendTransition.transition_preserved
