import PASoundness.PeanoBetaEndpointPairs
import PASoundness.PeanoInverseFutureAlignment

/-! The endpoint-pair inverse condition supplies the strict-future inverse
family used by the CRT step. The endpoint condition is an explicit PA premise;
this does not yet construct a full CRT code. -/
namespace PASoundness.PeanoBetaCRTFuturePair
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoBetaEndpointPairs

def endpointAt8 : Peano.Formula := FOL.substAt endpointUniform 7 (.var 8)
def pairBody : Peano.Formula := FOL.existsAt 3 (FOL.existsAt 4
  ((mul (modulus (.var 1) (.var 7)) (.var 3)).equal
    (add (succ zero) (mul (.var 4) (modulus (.var 1) (.var 2))))))
def rowAt5 : Peano.Formula := (less (.var 7) (.var 5)).imp
  ((less (.var 5) (succ (.var 8))).imp
    (FOL.existsAt 3 (FOL.existsAt 4
      ((mul (modulus (.var 1) (.var 7)) (.var 3)).equal
        (add (succ zero) (mul (.var 4) (modulus (.var 1) (.var 5))))))))
def outerBody : Peano.Formula := FOL.allAt 5
  ((less (.var 0) (.var 5)).imp ((less (.var 5) (succ (.var 8))).imp target))

/-- Rename only the free overall bound, before instantiating the index. -/
theorem endpoint_bound_syntax : endpointAt8 = FOL.allAt 0 outerBody := by
  simp [endpointAt8, endpointUniform, outerBody, target, targetBody,
    FOL.substAt, FOL.existsAt, FOL.allAt, less, lessTemplate, exAt, v, modulus,
    Peano.add, Peano.mul, Peano.succ, Peano.zero,
    FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux]
  repeat' first
    | rfl
    | constructor
    | (congr 1; funext i; fin_cases i <;>
        dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])

/-- Substitute the current index name 7 into the ordered-pair family. -/
theorem endpoint_current_syntax : FOL.substAt outerBody 0 (.var 7) = FOL.allAt 5 rowAt5 := by
  simp [FOL.substAt, outerBody, rowAt5, target, targetBody,
    FOL.existsAt, FOL.allAt, less, lessTemplate, exAt, v, modulus,
    Peano.add, Peano.mul, Peano.succ, Peano.zero,
    FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux]
  repeat' first
    | rfl
    | constructor
    | (congr 1; funext i; fin_cases i <;>
        dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])

/-- Substitute the target future-index name 2 into the inverse row. -/
theorem endpoint_future_syntax : FOL.substAt rowAt5 5 (.var 2) =
    (less (.var 7) (.var 2)).imp ((less (.var 2) (succ (.var 8))).imp pairBody) := by
  simp [FOL.substAt, rowAt5, pairBody,
    FOL.existsAt, FOL.allAt, less, lessTemplate, exAt, v, modulus,
    Peano.add, Peano.mul, Peano.succ, Peano.zero,
    FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux]
  repeat' first
    | rfl
    | constructor
    | (congr 1; funext i; fin_cases i <;>
        dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])

/-- The aligned strict-future pair family follows inside PA from the exact
ordered-endpoint condition after changing its bound name from 7 to 8. -/
theorem pair_family_of_endpoint : FormulaProves
    (endpointAt8.imp PeanoInverseFutureAlignment.pairFamily) := by
  let E := endpointAt8
  let G := PeanoInverseFutureAlignment.strictGuard
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.generalize 2
  · intro ψ hψ
    have h : ψ = E := by simpa using hψ
    subst ψ
    decide
  apply FOL.Context.deduction
  let Γ := [G,E]
  have he : FOL.Context Peano.Axiom Γ E := FOL.Context.under (FOL.Context.head [] E) G
  have hg : FOL.Context Peano.Axiom Γ G := FOL.Context.head _ _
  have hfirst : FOL.Context Peano.Axiom Γ (FOL.allAt 5 rowAt5) := by
    have h := FOL.Context.allElim (x := 0) (φ := outerBody) (by
      simpa only [E, endpoint_bound_syntax] using he) (.var 7)
    simpa only [endpoint_current_syntax] using h
  have hsecond : FOL.Context Peano.Axiom Γ
      ((less (.var 7) (.var 2)).imp ((less (.var 2) (succ (.var 8))).imp pairBody)) := by
    have h := FOL.Context.allElim (x := 5) (φ := rowAt5) hfirst (.var 2)
    simpa only [endpoint_future_syntax] using h
  have hlt : FOL.Context Peano.Axiom Γ (less (.var 7) (.var 2)) := FOL.Context.conjunctionLeft hg
  have hbound : FOL.Context Peano.Axiom Γ (less (.var 2) (.var 8)) := FOL.Context.conjunctionRight hg
  have hupper : FOL.Context Peano.Axiom Γ (less (.var 2) (succ (.var 8))) :=
    .mp (.mp (.closed (PeanoOrderTransitive.less_transitive_all (.var 2) (.var 8) (succ (.var 8)))) hbound)
      (.closed (PeanoPowerTransition.self_less_succ (.var 8)))
  have hp : FOL.Context Peano.Axiom Γ pairBody := .mp (.mp hsecond hlt) hupper
  exact hp

/-- The endpoint condition has only the beta parameter and the bound as free
names after the capture-safe bound renaming. -/
theorem endpoint_freeVars : endpointAt8.freeVarFinset = {1,8} := by decide

/-- Therefore the current code, product, and selected-witness names are fresh
in the endpoint condition. -/
theorem endpoint_fresh (x : Nat) (hx1 : x ≠ 1) (hx8 : x ≠ 8) :
    x ∉ endpointAt8.freeVarFinset := by
  simp [endpoint_freeVars, hx1, hx8]

/-- Compose the ordered-endpoint hypothesis with the existing product
inverse step, retaining an arbitrary additional side condition and the
selected local formula as explicit antecedents. -/
theorem future_component_with_side (φ side selected : Peano.Formula) : FormulaProves
    ((side ⊓ endpointAt8).imp ((PeanoBetaCRTInvariant.currentMatrix φ).imp (selected.imp
      (FOL.substAt (FOL.substAt PeanoBetaCRTInvariant.nextFuture 11
        PeanoBetaCRTAlignment.alignedCode) 12 PeanoBetaCRTAlignment.alignedProduct)))) := by
  let S := side ⊓ endpointAt8
  let C := PeanoBetaCRTInvariant.currentMatrix φ
  let W := selected
  let Γ := [W,C,S]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hs : FOL.Context Peano.Axiom Γ S :=
    FOL.Context.under (FOL.Context.under (FOL.Context.head [] S) C) W
  have hc : FOL.Context Peano.Axiom Γ C := FOL.Context.under (FOL.Context.head [S] C) W
  have he : FOL.Context Peano.Axiom Γ endpointAt8 := FOL.Context.conjunctionRight hs
  have hp : FOL.Context Peano.Axiom Γ PeanoInverseFutureAlignment.pairFamily :=
    .mp (.closed pair_family_of_endpoint) he
  exact .mp (.mp (.closed (PeanoInverseFutureAlignment.future_component_of_matrix φ)) hp) hc

end PASoundness.PeanoBetaCRTFuturePair
