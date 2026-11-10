import PASoundness.PeanoBetaCRTRecordStep
import PASoundness.PeanoCommonMultiple

/-! Merge the preserved beta-record prefix and its selected boundary record.
The row relation stays literally unchanged; state stability for later induction
is separate. No row-family or bounded CRT existence is asserted. -/
namespace PASoundness.PeanoBetaCRTRecordMerge
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic
open PeanoBetaUniformPreserve PeanoBetaCRTRecordStep

/-- The selected record is the chosen relation instance and actual beta row. -/
def selectedRecord (R : Peano.Formula) : Peano.Formula := (selected R) ⊓ selectedBeta

/-- The selected substitution removes free occurrence of the old index name,
even for a formula R with arbitrary other parameters. -/
theorem selected_index_fresh (R : Peano.Formula) : 2 ∉ (selected R).freeVarFinset := by
  intro h
  unfold selected at h
  rw [SyntaxTransport.formula_subst_freeVars] at h
  obtain ⟨y, _, hy⟩ := h
  split_ifs at hy with h2 h3 <;> simp_all

/-- The full selected record is also fresh for the old-index binder. -/
theorem selected_record_index_fresh (R : Peano.Formula) :
    2 ∉ (selectedRecord R).freeVarFinset := by
  have hb : 2 ∉ selectedBeta.freeVarFinset := by decide
  change 2 ∉ ((selected R).imp selectedBeta.not).not.freeVarFinset
  simp [FirstOrder.Language.BoundedFormula.freeVarFinset, selected_index_fresh, hb]

/-- The updated old family extended through the boundary at name 6. -/
def fullNewFamily (R : Peano.Formula) : Peano.Formula :=
  FOL.allAt 2 ((less (.var 2) (succ (.var 6))).imp (newExists R))

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

private theorem subst_not (φ : Peano.Formula) (σ : Nat → Peano.Term) :
    φ.not.subst σ = (φ.subst σ).not := by
  simp [FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.mapTermRel]
  rfl
private theorem subst_and (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ ⊓ ψ).subst σ = (φ.subst σ) ⊓ (ψ.subst σ) := by
  change (φ.imp ψ.not).not.subst σ = ((φ.subst σ).imp (ψ.subst σ).not).not
  rw [subst_not, show (φ.imp ψ.not).subst σ = (φ.subst σ).imp (ψ.not.subst σ) from rfl, subst_not]

private theorem selected_eq (R : Peano.Formula) :
    FOL.substAt (FOL.substAt R 3 (.var 8)) 2 (.var 6) = selected R := by
  unfold FOL.substAt selected
  rw [SyntaxTransport.formula_subst_comp]
  congr 1
  funext y
  by_cases h2 : y = 2 <;> by_cases h3 : y = 3 <;>
    simp [h2, h3, FirstOrder.Language.Term.subst]

theorem relation_transport (R : Peano.Formula) :
    FormulaProves (((.var 2 : Peano.Term).equal (.var 6)).imp
      ((selected R).imp (FOL.substAt R 3 (.var 8)))) := by
  let φ := FOL.substAt R 3 (.var 8)
  have he : FormulaProves (((.var 6 : Peano.Term).equal (.var 2)).imp
      ((FOL.substAt φ 2 (.var 6)).imp (FOL.substAt φ 2 (.var 2)))) :=
    .logical (.eqSubst φ 2 (.var 6) (.var 2))
  have hs : FormulaProves (((.var 2 : Peano.Term).equal (.var 6)).imp
      ((.var 6 : Peano.Term).equal (.var 2))) := FOL.equality_symmetry _ _
  have he' : FormulaProves (((.var 6 : Peano.Term).equal (.var 2)).imp
      ((selected R).imp φ)) := by
    simpa only [φ, selected_eq, SyntaxTransport.substAt_self] using he
  exact FOL.Derivation.compose hs he'

theorem beta_transport : FormulaProves (((.var 2 : Peano.Term).equal (.var 6)).imp
    (selectedBeta.imp (beta updatedCode (.var 1) (.var 2) (.var 8)))) := by
  let φ : Peano.Formula := beta updatedCode (.var 1) (.var 2) (.var 8)
  have he : FormulaProves (((.var 6 : Peano.Term).equal (.var 2)).imp
      ((FOL.substAt φ 2 (.var 6)).imp (FOL.substAt φ 2 (.var 2)))) :=
    .logical (.eqSubst φ 2 (.var 6) (.var 2))
  have hs : FormulaProves (((.var 2 : Peano.Term).equal (.var 6)).imp
      ((.var 6 : Peano.Term).equal (.var 2))) := FOL.equality_symmetry _ _
  have he' : FormulaProves (((.var 6 : Peano.Term).equal (.var 2)).imp
      (selectedBeta.imp φ)) := by
    simpa [φ, selectedBeta, FOL.substAt, beta_subst, updatedCode, increment,
      add_subst, mul_subst, succ_subst, FirstOrder.Language.Term.subst] using he
  exact FOL.Derivation.compose hs he'

private theorem target_sub (R : Peano.Formula) :
    FOL.substAt (R ⊓ updatedRow) 3 (.var 8) =
      (FOL.substAt R 3 (.var 8)) ⊓ beta updatedCode (.var 1) (.var 2) (.var 8) := by
  simp [FOL.substAt, subst_and, updatedRow, beta_subst, updatedCode, increment,
    add_subst, mul_subst, succ_subst, FirstOrder.Language.Term.subst]

theorem boundary_witness (R : Peano.Formula) : FormulaProves
    (((.var 2 : Peano.Term).equal (.var 6)).imp
      ((selected R).imp (selectedBeta.imp (newExists R)))) := by
  let E : Peano.Formula := (.var 2 : Peano.Term).equal (.var 6)
  let Γ := [selectedBeta, selected R, E]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have he : FOL.Context Peano.Axiom Γ E := .hypothesis (by simp [Γ])
  have hr : FOL.Context Peano.Axiom Γ (selected R) := .hypothesis (by simp [Γ])
  have hb : FOL.Context Peano.Axiom Γ selectedBeta := FOL.Context.head _ _
  have hr' : FOL.Context Peano.Axiom Γ (FOL.substAt R 3 (.var 8)) :=
    .mp (.mp (.closed (relation_transport R)) he) hr
  have hb' : FOL.Context Peano.Axiom Γ (beta updatedCode (.var 1) (.var 2) (.var 8)) :=
    .mp (.mp (.closed beta_transport) he) hb
  have hw : FOL.Context Peano.Axiom Γ (FOL.substAt (R ⊓ updatedRow) 3 (.var 8)) := by
    rw [target_sub]
    exact FOL.Context.conjunctionIntro hr' hb'
  exact .mp (.closed (FOL.Derivation.existsIntro (R ⊓ updatedRow) 3 (.var 8))) hw

/-- Conditional quantifier merger. The literal boundary derivation and its
freshness condition are discharged separately. -/
theorem merge_of_boundary (R : Peano.Formula)
    (hfree : 2 ∉ (selectedRecord R).freeVarFinset)
    (hboundary : FormulaProves (((.var 2 : Peano.Term).equal (.var 6)).imp
      ((selectedRecord R).imp (newExists R)))) :
    FormulaProves ((newFamily R).imp ((selectedRecord R).imp (fullNewFamily R))) := by
  let E := (.var 2 : Peano.Term).equal (.var 6)
  let L := less (.var 2) (.var 6)
  let L' := less (.var 2) (succ (.var 6))
  let Γ := [L', selectedRecord R, newFamily R]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.generalize 2
  · intro ψ hψ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hψ
    rcases hψ with rfl | rfl
    · exact hfree
    · simp [newFamily]
  apply FOL.Context.deduction
  have hsmall : FOL.Context Peano.Axiom Γ L' := FOL.Context.head _ _
  have hsel : FOL.Context Peano.Axiom Γ (selectedRecord R) := .hypothesis (by simp [Γ])
  have hold : FOL.Context Peano.Axiom Γ (newFamily R) := .hypothesis (by simp [Γ])
  have hcases : FOL.Context Peano.Axiom Γ (E ⊔ L) :=
    .mp (.closed (PeanoCommonMultiple.BoundSplit.less_successor_cases (.var 2) (.var 6))) hsmall
  have he : FOL.Context Peano.Axiom Γ (E.imp (newExists R)) := by
    apply FOL.Context.deduction
    have heq : FOL.Context Peano.Axiom (E :: Γ) E := FOL.Context.head _ _
    exact .mp (.mp (.closed hboundary) heq) (FOL.Context.under hsel E)
  have hl : FOL.Context Peano.Axiom Γ (L.imp (newExists R)) := FOL.Context.allSelf hold
  exact or_elim hcases he hl

/-- Put the selected boundary witness into a single existential row. -/
theorem boundary_record (R : Peano.Formula) :
    FormulaProves (((.var 2 : Peano.Term).equal (.var 6)).imp
      ((selectedRecord R).imp (newExists R))) := by
  let E : Peano.Formula := (.var 2 : Peano.Term).equal (.var 6)
  let Γ := [selectedRecord R, E]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have he : FOL.Context Peano.Axiom Γ E := FOL.Context.under (FOL.Context.head [] E) (selectedRecord R)
  have hs : FOL.Context Peano.Axiom Γ (selectedRecord R) := FOL.Context.head _ _
  have hr : FOL.Context Peano.Axiom Γ (selected R) := FOL.Context.conjunctionLeft hs
  have hb : FOL.Context Peano.Axiom Γ selectedBeta := FOL.Context.conjunctionRight hs
  exact .mp (.mp (.mp (.closed (boundary_witness R)) he) hr) hb

/-- Merge the old-index record family and the selected record into the family
for all indices below the successor of the current bound. -/
theorem merge (R : Peano.Formula) :
    FormulaProves ((newFamily R).imp ((selectedRecord R).imp (fullNewFamily R))) :=
  merge_of_boundary R (selected_record_index_fresh R) (boundary_record R)

/-- Complete this single record step: under the explicit old-family,
selected-relation, divisibility, certificate and bound hypotheses, all rows
through the current boundary have witnesses after the update. R stays literally
unchanged, including any references to code, product, or bound state names. -/
theorem full_record_step (R : Peano.Formula) : FormulaProves
    (boundedDivisors.imp ((oldFamily R).imp ((selected R).imp
      (certificate.imp (selectedBound.imp (fullNewFamily R)))))) := by
  let Γ := [selectedBound, certificate, selected R, oldFamily R, boundedDivisors]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hdiv : FOL.Context Peano.Axiom Γ boundedDivisors := .hypothesis (by simp [Γ])
  have hold : FOL.Context Peano.Axiom Γ (oldFamily R) := .hypothesis (by simp [Γ])
  have hsel : FOL.Context Peano.Axiom Γ (selected R) := .hypothesis (by simp [Γ])
  have hcert : FOL.Context Peano.Axiom Γ certificate := .hypothesis (by simp [Γ])
  have hbd : FOL.Context Peano.Axiom Γ selectedBound := FOL.Context.head _ _
  have hstep : FOL.Context Peano.Axiom Γ ((newFamily R) ⊓ selectedRecord R) :=
    .mp (.mp (.mp (.mp (.mp (.closed (preserve_and_install R)) hdiv) hold) hsel) hcert) hbd
  exact .mp (.mp (.closed (merge R)) (FOL.Context.conjunctionLeft hstep))
    (FOL.Context.conjunctionRight hstep)

end PASoundness.PeanoBetaCRTRecordMerge
