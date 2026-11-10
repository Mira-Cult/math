import PASoundness.PeanoFiniteComprehensionBase

/-! Fixed-name singleton-selector lemmas for the AX8 index-alias case. The
literal alias reduction and existential witness construction are separate. -/
namespace PASoundness.PeanoAX8SingletonSelector
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

/-- Name 1 is the quantified index, name 5 is the separately retained outer
index. The formula ψ may have arbitrary free parameters. -/
def selector (ψ : Peano.Formula) : Peano.Formula :=
  ((.var 1 : Peano.Term).equal (.var 5)) ⊓ ψ

/-- Output code name 3 realizes exactly the singleton selector. -/
def globalRows (ψ : Peano.Formula) : Peano.Formula :=
  FOL.allAt 1 (((bitFormula (.var 3) (.var 1)).imp (selector ψ)) ⊓
    ((selector ψ).imp (bitFormula (.var 3) (.var 1))))

/-- A bounded outer index bounds every instance of the singleton selector. -/
theorem selector_bounded (ψ : Peano.Formula) : FormulaProves
    ((less (.var 5) (.var 0)).imp
      (FOL.allAt 1 ((selector ψ).imp (less (.var 1) (.var 0))))) := by
  let H := less (.var 5) (.var 0)
  let S := selector ψ
  let E := (.var 1 : Peano.Term).equal (.var 5)
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.generalize 1
  · intro φ hφ
    have he : φ = H := by simpa using hφ
    subst φ
    decide
  apply FOL.Context.deduction
  let Γ := [S, H]
  have hs : FOL.Context Peano.Axiom Γ S := .head _ _
  have hh : FOL.Context Peano.Axiom Γ H := .hypothesis (by simp [Γ])
  have he : FOL.Context Peano.Axiom Γ E := FOL.Context.conjunctionLeft hs
  exact .mp (.mp (.closed (PeanoQuotientGap.less_left_congr
    (.var 5) (.var 1) (.var 0))) (FOL.Context.eqSymm he)) hh

/-- Every set output bit satisfies ψ; ψ can still contain other parameters. -/
theorem output_implies_relation (ψ : Peano.Formula) : FormulaProves
    ((globalRows ψ).imp (FOL.allAt 1 ((bitFormula (.var 3) (.var 1)).imp ψ))) := by
  let G := globalRows ψ
  let B := bitFormula (.var 3) (.var 1)
  let S := selector ψ
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.generalize 1
  · intro φ hφ
    have he : φ = G := by simpa using hφ
    subst φ
    simp [G, globalRows, SyntaxTransport.allAt_freeVars]
  apply FOL.Context.deduction
  let Γ := [B, G]
  have hb : FOL.Context Peano.Axiom Γ B := .head _ _
  have hg : FOL.Context Peano.Axiom Γ G := .hypothesis (by simp [Γ])
  have hi : FOL.Context Peano.Axiom Γ ((B.imp S) ⊓ (S.imp B)) := FOL.Context.allSelf hg
  exact FOL.Context.conjunctionRight (.mp (FOL.Context.conjunctionLeft hi) hb)

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := rfl

private theorem subst_not (φ : Peano.Formula) (σ : Nat → Peano.Term) :
    φ.not.subst σ = (φ.subst σ).not := by
  simp [FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.mapTermRel]
  rfl

private theorem subst_and (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ ⊓ ψ).subst σ = (φ.subst σ) ⊓ (ψ.subst σ) := by
  change (φ.imp ψ.not).not.subst σ = ((φ.subst σ).imp (ψ.subst σ).not).not
  rw [subst_not, subst_imp, subst_not]

/-- At the separately retained outer index 5, the capture-safe instance
ψ[1:=5] implies that the selected output bit is present. -/
theorem outer_relation_implies_bit (ψ : Peano.Formula) : FormulaProves
    ((globalRows ψ).imp ((FOL.substAt ψ 1 (.var 5)).imp
      (bitFormula (.var 3) (.var 5)))) := by
  let G := globalRows ψ
  let Q := FOL.substAt ψ 1 (.var 5)
  let E := (.var 5 : Peano.Term).equal (.var 5)
  let B := bitFormula (.var 3) (.var 5)
  let body := ((bitFormula (.var 3) (.var 1)).imp (selector ψ)) ⊓
    ((selector ψ).imp (bitFormula (.var 3) (.var 1)))
  have hsyntax : FOL.substAt body 1 (.var 5) =
      ((B.imp (E ⊓ Q)) ⊓ ((E ⊓ Q).imp B)) := by
    simp [FOL.substAt, body, B, E, Q, selector, subst_and, subst_imp,
      FOL.equality_subst, bitFormula_subst, FirstOrder.Language.Term.subst]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let Γ := [Q, G]
  have hg : FOL.Context Peano.Axiom Γ G := .hypothesis (by simp [Γ])
  have hq : FOL.Context Peano.Axiom Γ Q := .head _ _
  have hi : FOL.Context Peano.Axiom Γ ((B.imp (E ⊓ Q)) ⊓ ((E ⊓ Q).imp B)) := by
    have h := FOL.Context.allElim (x := 1) (φ := body) hg (.var 5)
    simpa only [hsyntax] using h
  have he : FOL.Context Peano.Axiom Γ E := .closed (.logical (.eqRefl (.var 5)))
  exact .mp (FOL.Context.conjunctionRight hi) (FOL.Context.conjunctionIntro he hq)

end PASoundness.PeanoAX8SingletonSelector

#print axioms PASoundness.PeanoAX8SingletonSelector.selector_bounded
#print axioms PASoundness.PeanoAX8SingletonSelector.output_implies_relation
#print axioms PASoundness.PeanoAX8SingletonSelector.outer_relation_implies_bit
