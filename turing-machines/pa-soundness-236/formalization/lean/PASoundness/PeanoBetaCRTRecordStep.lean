import PASoundness.PeanoBetaUniformPreserve
import PASoundness.PeanoBetaBoundedDivisibility
import PASoundness.PeanoBetaInverseAppend

/-! A fixed-name PA beta-record invariant step. Old-row witnesses, the selected
new row, bounded divisibility and inverse certificate remain explicit inputs;
this is not a bounded CRT existence or trace-extension theorem. -/
namespace PASoundness.PeanoBetaCRTRecordStep
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic
open PeanoBetaUniformPreserve

/-- The update uses code 0, parameter 1, product 4, current index 6, selected
value 8, and inverse witness 9. Bound index 2 and row value 3 are not free in
the increment. -/
def increment : Peano.Term :=
  mul (.var 4) (mul (.var 9)
    (add (.var 8) (mul (mul (succ (.var 6)) (.var 1)) (.var 0))))

def updatedCode : Peano.Term := add (.var 0) increment

def updatedRow : Peano.Formula := beta updatedCode (.var 1) (.var 2) (.var 3)

def selectedBeta : Peano.Formula := beta updatedCode (.var 1) (.var 6) (.var 8)

def certificate : Peano.Formula :=
  (mul (.var 4) (.var 9)).equal
    (add (succ zero) (mul (.var 10) (modulus (.var 1) (.var 6))))

def selectedBound : Peano.Formula := less (.var 8) (modulus (.var 1) (.var 6))

/-- Capture-safe selected instance of a desired row relation: index name 2 is
replaced by 6 and row-value name 3 by 8, simultaneously. -/
def selected (R : Peano.Formula) : Peano.Formula :=
  R.subst (fun x => if x = 2 then .var 6 else if x = 3 then .var 8 else .var x)

/-- The capture-safe selected formula has the intended assignment semantics;
this separate theorem does not construct any object-level PA proof. -/
theorem selected_realize (R : Peano.Formula) (ρ : Nat → Nat) :
    (selected R).Realize ρ ↔
      R.Realize (fun x => if x = 2 then ρ 6 else if x = 3 then ρ 8 else ρ x) := by
  simp only [selected, FOL.realize_subst]
  have henv : (fun x => (if x = 2 then (.var 6 : Peano.Term)
      else if x = 3 then .var 8 else .var x).realize ρ) =
      (fun x => if x = 2 then ρ 6 else if x = 3 then ρ 8 else ρ x) := by
    funext x
    split_ifs <;> rfl
  rw [henv]

/-- The selected record is installed by the literal beta append lemma, while
retaining the explicitly supplied desired-row formula. -/
theorem selected_record (R : Peano.Formula) : FormulaProves
    ((selected R).imp (certificate.imp (selectedBound.imp ((selected R) ⊓ selectedBeta)))) := by
  let Γ := [selectedBound, certificate, selected R]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hr : FOL.Context Peano.Axiom Γ (selected R) := .hypothesis (by simp [Γ])
  have he : FOL.Context Peano.Axiom Γ certificate := .hypothesis (by simp [Γ])
  have hb : FOL.Context Peano.Axiom Γ selectedBound := FOL.Context.head _ _
  have hbeta : FOL.Context Peano.Axiom Γ selectedBeta :=
    .mp (.mp (.closed (PeanoBetaInverseAppend.beta_append_literal
      (.var 0) (.var 4) (.var 9) (.var 10) (.var 1) (.var 6) (.var 8))) he) hb
  exact FOL.Context.conjunctionIntro hr hbeta


/-- The old bounded-row divisibility condition, now for the explicit increment. -/
def incrementDivisors : Peano.Formula :=
  FOL.allAt 2 ((less (.var 2) (.var 6)).imp
    (PeanoDivisibility.divides (modulus (.var 1) (.var 2)) increment))

/-- Every old row, at every value, is preserved by the explicit increment. -/
def pointwisePreservation : Peano.Formula :=
  FOL.allAt 2 (FOL.allAt 3 ((less (.var 2) (.var 6)).imp (oldRow.imp updatedRow)))

private theorem divides_subst (k d : Peano.Term) (σ : Nat → Peano.Term) :
    (PeanoDivisibility.divides k d).subst σ =
      PeanoDivisibility.divides (k.subst σ) (d.subst σ) := by
  unfold PeanoDivisibility.divides
  rw [SyntaxTransport.formula_subst_comp]
  congr 1
  funext y
  by_cases h0 : y = 0 <;> by_cases h1 : y = 1 <;> simp [h0, h1]

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := by rfl

/-- Specialize the pointwise row-preservation derivation to the actual append
increment. Name 4 remains free inside the chosen increment term. -/
theorem concrete_pointwise : FormulaProves
    ((PeanoDivisibility.divides (modulus (.var 1) (.var 2)) increment).imp
      (oldRow.imp updatedRow)) := by
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom)
      (.allElim ((PeanoDivisibility.divides (modulus (.var 1) (.var 2)) (.var 4)).imp
        (oldRow.imp newRow)) 4 increment))
    (FOL.Derivation.generalize 4 divisible_row_preserved)
  simpa [FOL.substAt, subst_imp, oldRow, newRow, updatedRow, updatedCode, divides_subst,
    beta_subst, modulus, mul_subst, add_subst, succ_subst, FirstOrder.Language.Term.subst] using h

/-- The explicit increment preserves every old row under its bounded
divisibility hypothesis. -/
theorem increment_preserves_rows : FormulaProves
    (incrementDivisors.imp pointwisePreservation) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.generalize 2
  · intro ψ hψ
    have h : ψ = incrementDivisors := by simpa using hψ
    subst ψ
    decide
  apply FOL.Context.generalize 3
  · intro ψ hψ
    have h : ψ = incrementDivisors := by simpa using hψ
    subst ψ
    decide
  apply FOL.Context.deduction
  let L := less (.var 2) (.var 6)
  let D := PeanoDivisibility.divides (modulus (.var 1) (.var 2)) increment
  let Γ := [L, incrementDivisors]
  have hbound : FOL.Context Peano.Axiom Γ incrementDivisors :=
    FOL.Context.under (FOL.Context.head [] incrementDivisors) L
  have hsmall : FOL.Context Peano.Axiom Γ L := FOL.Context.head _ _
  have hdiv : FOL.Context Peano.Axiom Γ D := .mp (FOL.Context.allSelf hbound) hsmall
  exact .mp (.closed concrete_pointwise) hdiv

def bound : Peano.Formula := less (.var 2) (.var 6)
def oldExists (R : Peano.Formula) : Peano.Formula := FOL.existsAt 3 (R ⊓ oldRow)
def newExists (R : Peano.Formula) : Peano.Formula := FOL.existsAt 3 (R ⊓ updatedRow)
def oldFamily (R : Peano.Formula) : Peano.Formula := FOL.allAt 2 (bound.imp (oldExists R))
def newFamily (R : Peano.Formula) : Peano.Formula := FOL.allAt 2 (bound.imp (newExists R))

/-- The same row witness serves after the pointwise preservation implication. -/
theorem matrix_to_target (R : Peano.Formula) :
    FormulaProves ((R ⊓ oldRow).imp (pointwisePreservation.imp (bound.imp (newExists R)))) := by
  let Γ := [bound, pointwisePreservation, R ⊓ oldRow]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hb : FOL.Context Peano.Axiom Γ bound := FOL.Context.head _ _
  have hp : FOL.Context Peano.Axiom Γ pointwisePreservation := .hypothesis (by simp [Γ])
  have hr : FOL.Context Peano.Axiom Γ (R ⊓ oldRow) := .hypothesis (by simp [Γ])
  have hR : FOL.Context Peano.Axiom Γ R := FOL.Context.conjunctionLeft hr
  have ho : FOL.Context Peano.Axiom Γ oldRow := FOL.Context.conjunctionRight hr
  have hn : FOL.Context Peano.Axiom Γ updatedRow :=
    .mp (.mp (FOL.Context.allSelf (FOL.Context.allSelf hp)) hb) ho
  have hbody : FOL.Context Peano.Axiom Γ (R ⊓ updatedRow) := FOL.Context.conjunctionIntro hR hn
  have hintro := FOL.Derivation.existsIntro (A := Peano.Axiom) (R ⊓ updatedRow) 3 (.var 3)
  have hintro' : FormulaProves ((R ⊓ updatedRow).imp (newExists R)) := by
    simpa only [SyntaxTransport.substAt_self, newExists] using hintro
  exact .mp (.closed hintro') hbody

/-- Eliminate the old row witness; it is absent from the entire conclusion. -/
theorem old_exists_to_target (R : Peano.Formula) :
    FormulaProves ((oldExists R).imp (pointwisePreservation.imp (bound.imp (newExists R)))) := by
  have hbound : 3 ∉ bound.freeVarFinset := by decide
  have fresh : 3 ∉ (pointwisePreservation.imp (bound.imp (newExists R))).freeVarFinset := by
    simp [pointwisePreservation, newExists, FOL.existsAt, hbound]
  exact PeanoBitPositionReduction.exists_elim 3 fresh (matrix_to_target R)

/-- Reuse each witness in any unchanged desired-row formula. Any references
in R to state variables, including code 0, product 4, or bound 6, remain
unchanged; later induction requires a separate stability or substitution step. -/
theorem preserve_family (R : Peano.Formula) :
    FormulaProves (pointwisePreservation.imp ((oldFamily R).imp (newFamily R))) := by
  let Γ := [bound, oldFamily R, pointwisePreservation]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.generalize 2
  · intro ψ hψ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hψ
    rcases hψ with rfl | rfl <;> simp [oldFamily, pointwisePreservation]
  apply FOL.Context.deduction
  have hb : FOL.Context Peano.Axiom Γ bound := FOL.Context.head _ _
  have hp : FOL.Context Peano.Axiom Γ pointwisePreservation := .hypothesis (by simp [Γ])
  have ho : FOL.Context Peano.Axiom Γ (oldFamily R) := .hypothesis (by simp [Γ])
  have hex : FOL.Context Peano.Axiom Γ (oldExists R) := .mp (FOL.Context.allSelf ho) hb
  exact .mp (.mp (.mp (.closed (old_exists_to_target R)) hex) hp) hb

/-- The exact CRT append step preserves the old bounded record family and
installs the selected new record. It retains explicit bounded divisibility,
old-family, selected-relation, inverse-certificate and remainder-bound premises;
it does not assert existence of those witnesses or any whole induction. -/
theorem preserve_and_install (R : Peano.Formula) : FormulaProves
    (boundedDivisors.imp ((oldFamily R).imp ((selected R).imp
      (certificate.imp (selectedBound.imp ((newFamily R) ⊓ ((selected R) ⊓ selectedBeta))))))) := by
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
  have hinc : FOL.Context Peano.Axiom Γ incrementDivisors :=
    .mp (.closed PeanoBetaBoundedDivisibility.bounded_divides_boundary_increment) hdiv
  have hpoint : FOL.Context Peano.Axiom Γ pointwisePreservation :=
    .mp (.closed increment_preserves_rows) hinc
  have hnew : FOL.Context Peano.Axiom Γ (newFamily R) :=
    .mp (.mp (.closed (preserve_family R)) hpoint) hold
  have hselected : FOL.Context Peano.Axiom Γ ((selected R) ⊓ selectedBeta) :=
    .mp (.mp (.mp (.closed (selected_record R)) hsel) hcert) hbd
  exact FOL.Context.conjunctionIntro hnew hselected

end PASoundness.PeanoBetaCRTRecordStep
