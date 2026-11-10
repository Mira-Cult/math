import PASoundness.PeanoBetaAppendEndTransition
import PASoundness.PeanoBetaAppendTraceFamily
import PASoundness.PeanoBetaCRTAlpha

/-! PA endpoint transition as the existential row formula used by the trace
family, conditional on an existing recoding row family and old endpoint. -/
namespace PASoundness.PeanoBetaAppendEndFamily
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoBetaAppendRelation PeanoBetaCRTInvariant
open PeanoBetaAppendTraceFamily PeanoBetaAppendEndTransition

/-- Literal transition formula, with value witnesses 20 and 21. -/
def F : Peano.Formula := FOL.existsAt 20 (FOL.existsAt 21 newBody)

private theorem subst_imp (φ ψ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    FOL.substAt (φ.imp ψ) x t = (FOL.substAt φ x t).imp (FOL.substAt ψ x t) := rfl
private theorem subst_and (φ ψ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    FOL.substAt (φ ⊓ ψ) x t = (FOL.substAt φ x t) ⊓ (FOL.substAt ψ x t) := rfl

private def endpointBody := FOL.substAt newBody 2 (.var 0)
private def endpointBodyR := FOL.substAt endpointBody 20 (.var 6)
private def endpointBodyRS := FOL.substAt endpointBodyR 21 (add (.var 6) (.var 6))

private theorem endpoint_target : FOL.substAt F 2 (.var 0) =
    FOL.existsAt 20 (FOL.existsAt 21 endpointBody) := by
  rw [F, PeanoBetaCRTAlpha.subst_var_existsAt _ 2 0 20 (by decide) (by decide),
    PeanoBetaCRTAlpha.subst_var_existsAt _ 2 0 21 (by decide) (by decide)]
  rfl

private theorem endpoint_inst20 : FOL.substAt (FOL.existsAt 21 endpointBody) 20 (.var 6) =
    FOL.existsAt 21 endpointBodyR := by
  rw [PeanoBetaCRTAlpha.subst_var_existsAt _ 20 6 21 (by decide) (by decide)]
  rfl

private theorem endpoint_inst_body : endpointBodyRS =
    ((beta (.var 9) (.var 1) (.var 0) (.var 6)) ⊓
      ((beta (.var 9) (.var 1) (succ (.var 0)) (add (.var 6) (.var 6))) ⊓
        ((add (.var 6) (.var 6)).equal (add (.var 6) (.var 6))))) := by
  dsimp only [endpointBodyRS, endpointBodyR, endpointBody, newBody, PeanoBetaAppendTransition.N]
  simp only [subst_and]
  simp [FOL.substAt, beta_subst,
    FOL.equality_subst, add_subst, succ_subst, FirstOrder.Language.Term.subst]

/-- The bounded recoding family provides its rows at n and S n. -/
theorem rows_at_endpoint : FormulaProves
    (recodedRows.imp (endpointRow ⊓ appendedRow)) := by
  let G := (less (.var 2) (succ (succ (.var 0)))).imp row
  let Γ := [recodedRows]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have hg : FOL.Context Peano.Axiom Γ recodedRows := FOL.Context.head _ _
  have h₀ : FOL.Context Peano.Axiom Γ (FOL.substAt G 2 (.var 0)) :=
    .mp (.closed (.logical (.allElim G 2 (.var 0)))) hg
  have h₁ : FOL.Context Peano.Axiom Γ (FOL.substAt G 2 (succ (.var 0))) :=
    .mp (.closed (.logical (.allElim G 2 (succ (.var 0))))) hg
  dsimp only [G] at h₀ h₁
  rw [subst_imp] at h₀ h₁
  have h₀' : FOL.Context Peano.Axiom Γ
      ((less (.var 0) (succ (succ (.var 0)))).imp endpointRow) := by
    simpa [G, endpointRow, subst_imp, FOL.substAt, less_subst, succ_subst,
      FirstOrder.Language.Term.subst] using h₀
  have h₁' : FOL.Context Peano.Axiom Γ
      ((less (succ (.var 0)) (succ (succ (.var 0)))).imp appendedRow) := by
    simpa [G, appendedRow, subst_imp, FOL.substAt, less_subst, succ_subst,
      FirstOrder.Language.Term.subst] using h₁
  have hlt : FOL.Context Peano.Axiom Γ (less (.var 0) (succ (succ (.var 0)))) :=
    .mp (.mp (.closed (PeanoOrderTransitive.less_transitive_all
      (.var 0) (succ (.var 0)) (succ (succ (.var 0)))))
        (.closed (PeanoPowerTransition.self_less_succ (.var 0))))
      (.closed (PeanoPowerTransition.self_less_succ (succ (.var 0))))
  have hr : FOL.Context Peano.Axiom Γ endpointRow := .mp h₀' hlt
  have hs : FOL.Context Peano.Axiom Γ appendedRow :=
    .mp h₁' (.closed (PeanoPowerTransition.self_less_succ (succ (.var 0))))
  exact FOL.Context.conjunctionIntro hr hs

/-- A supplied recoding-row family and the original endpoint yield the exact
capture-safe transition formula `F` at n. The two existential witnesses are
p and p+p; the theorem does not assert existence of a recoding family. -/
theorem endpoint_family : FormulaProves
    (recodedRows.imp ((beta (.var 4) (.var 5) (.var 0) (.var 6)).imp
      (FOL.substAt F 2 (.var 0)))) := by
  let E := beta (.var 4) (.var 5) (.var 0) (.var 6)
  let Γ := [E, recodedRows]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hg : FOL.Context Peano.Axiom Γ recodedRows := .hypothesis (by simp [Γ])
  have he : FOL.Context Peano.Axiom Γ E := FOL.Context.head _ _
  have hrows : FOL.Context Peano.Axiom Γ (endpointRow ⊓ appendedRow) :=
    .mp (.closed rows_at_endpoint) hg
  have hr : FOL.Context Peano.Axiom Γ endpointRow := FOL.Context.conjunctionLeft hrows
  have hs : FOL.Context Peano.Axiom Γ appendedRow := FOL.Context.conjunctionRight hrows
  have hb : FOL.Context Peano.Axiom Γ endpointBodyRS := by
    rw [endpoint_inst_body]
    exact .mp (.mp (.mp (.closed endpoint_doubling) hr) hs) he
  have hi21 := FOL.Derivation.existsIntro (A := Peano.Axiom) endpointBodyR 21
    (add (.var 6) (.var 6))
  have hi20 := FOL.Derivation.existsIntro (A := Peano.Axiom) (FOL.existsAt 21 endpointBody) 20 (.var 6)
  rw [endpoint_target]
  exact .mp (.closed (by rw [endpoint_inst20] at hi20; exact hi20))
    (.mp (.closed hi21) hb)

/-- The same supplied family also gives the new row at S n with output p+p. -/
theorem appended_output : FormulaProves
    (recodedRows.imp ((beta (.var 4) (.var 5) (.var 0) (.var 6)).imp
      (beta (.var 9) (.var 1) (succ (.var 0)) (add (.var 6) (.var 6))))) := by
  let E := beta (.var 4) (.var 5) (.var 0) (.var 6)
  let Γ := [E, recodedRows]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hg : FOL.Context Peano.Axiom Γ recodedRows := .hypothesis (by simp [Γ])
  have he : FOL.Context Peano.Axiom Γ E := FOL.Context.head _ _
  have hr := FOL.Context.conjunctionLeft (.mp (.closed rows_at_endpoint) hg)
  have hs := FOL.Context.conjunctionRight (.mp (.closed rows_at_endpoint) hg)
  exact FOL.Context.conjunctionLeft (FOL.Context.conjunctionRight
    (.mp (.mp (.mp (.closed endpoint_doubling) hr) hs) he))

end PASoundness.PeanoBetaAppendEndFamily

#print axioms PASoundness.PeanoBetaAppendEndFamily.endpoint_family

#print axioms PASoundness.PeanoBetaAppendEndFamily.appended_output
