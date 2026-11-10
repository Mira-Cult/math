import PASoundness.Peano

/-! Elementary theory controls in one fixed arithmetic signature.

The singleton model interprets every function symbol as its unique value. It
models the bare theory `forall x, x = 0`; it does not model PA. The same axiom
is false under the standard arithmetic interpretation on Nat. This is the
intended distinction between consistency and standard-model soundness.
-/

namespace PASoundness.Fixtures

open FirstOrder FirstOrder.Language
open Peano

def closedZero : language.Term Empty := .func .zero Fin.elim0

def reflexive : Sentence := .all (.equal (.var (.inr 0)) (.var (.inr 0)))
def allZero : Sentence := .all (.equal (.var (.inr 0)) (.func .zero Fin.elim0))
def falseZero : Sentence := (closedZero.equal closedZero).not
def collapsedSuccessor : Sentence :=
  ((.func .succ ![closedZero] : language.Term Empty).equal closedZero)

def emptyTheory : Sentence → Prop := fun _ => False
def oneAxiom (φ : Sentence) : Sentence → Prop := fun ψ => ψ = φ

instance unitStructure : language.Structure Unit where
  funMap := fun {_} _ _ => ()
  RelMap := fun {_} r => Empty.elim r

theorem empty_sound {φ : Sentence} (h : FOL.Proves emptyTheory φ) : Nat ⊨ φ :=
  FOL.theory_sound (fun _ hx => False.elim hx) h

theorem reflexive_nat : Nat ⊨ reflexive := by
  simp [reflexive, Sentence.Realize, FirstOrder.Language.Formula.Realize,
    BoundedFormula.Realize, Term.realize]

theorem harmless_sound {φ : Sentence} (h : FOL.Proves (oneAxiom reflexive) φ) :
    Nat ⊨ φ := by
  apply FOL.theory_sound (M := Nat) ?_ h
  intro ψ hψ
  cases hψ
  exact reflexive_nat

theorem allZero_unit : Unit ⊨ allZero := by
  simp [allZero, Sentence.Realize, FirstOrder.Language.Formula.Realize,
    BoundedFormula.Realize, Term.realize]

theorem allZero_not_nat : ¬ Nat ⊨ allZero := by
  intro h
  have h1 := h 1
  exact Nat.one_ne_zero h1

/-- A genuine consistency proof using a structure, with no PA axioms added. -/
theorem allZero_consistent : ¬ FOL.Proves (oneAxiom allZero) (⊥ : Sentence) := by
  apply FOL.theory_consistent (M := Unit)
  intro φ hφ
  cases hφ
  exact allZero_unit

/-- The same consistent theory has a false standard-Nat theorem. -/
theorem allZero_unsound :
    ∃ φ : Sentence, FOL.Proves (oneAxiom allZero) φ ∧ ¬ Nat ⊨ φ :=
  ⟨allZero, FOL.sentence_axiom rfl, allZero_not_nat⟩

/-- Even quantifier-free standard-Nat unsoundness need not be inconsistency
for a bare first-order theory. This theory includes no PA arithmetic axioms. -/
theorem collapsedSuccessor_consistent :
    ¬ FOL.Proves (oneAxiom collapsedSuccessor) (⊥ : Sentence) := by
  apply FOL.theory_consistent (M := Unit)
  intro φ hφ
  cases hφ
  exact rfl

theorem collapsedSuccessor_not_nat : ¬ Nat ⊨ collapsedSuccessor := by
  intro h
  exact Nat.one_ne_zero h

theorem collapsedSuccessor_unsound :
    ∃ φ : Sentence, FOL.Proves (oneAxiom collapsedSuccessor) φ ∧ ¬ Nat ⊨ φ :=
  ⟨collapsedSuccessor, FOL.sentence_axiom rfl, collapsedSuccessor_not_nat⟩

theorem falseZero_not_nat : ¬ Nat ⊨ falseZero := by
  intro h
  exact h rfl

theorem falseZero_unsound :
    ∃ φ : Sentence, FOL.Proves (oneAxiom falseZero) φ ∧ ¬ Nat ⊨ φ :=
  ⟨falseZero, FOL.sentence_axiom rfl, falseZero_not_nat⟩

theorem open_zero_eq : FOL.openSentence (closedZero.equal closedZero) =
    Peano.zero.equal Peano.zero := by
  simp [FOL.openSentence, FirstOrder.Language.Formula.relabel, BoundedFormula.relabel,
    BoundedFormula.mapTermRel, Term.equal, Term.bdEqual, closedZero, Peano.zero]
  congr 1
  funext i
  exact Fin.elim0 i

theorem falseZero_inconsistent : FOL.Proves (oneAxiom falseZero) (⊥ : Sentence) := by
  have ha : FOL.Derivation (FOL.SentenceAxiom (oneAxiom falseZero))
      (FOL.openSentence falseZero) := FOL.Derivation.axiom ⟨falseZero, rfl, rfl⟩
  have he : FOL.Derivation (FOL.SentenceAxiom (oneAxiom falseZero))
      (FOL.openSentence (closedZero.equal closedZero)) :=
    open_zero_eq.symm ▸ FOL.Derivation.logical (FOL.LogicalAxiom.eqRefl Peano.zero)
  exact FOL.Derivation.mp ha he

theorem pa_zero_reflexive : Peano.Proves (closedZero.equal closedZero) := by
  change FOL.Derivation Peano.Axiom (FOL.openSentence (closedZero.equal closedZero))
  rw [open_zero_eq]
  exact FOL.Derivation.logical (FOL.LogicalAxiom.eqRefl Peano.zero)

/-- A genuine PA axiom followed by generalization, as a finite derivation tree. -/
theorem pa_successor_nonzero :
    Peano.FormulaProves (FOL.allAt 0 (((Peano.succ (.var 0)).equal Peano.zero).not)) :=
  FOL.Derivation.generalize 0 (FOL.Derivation.axiom (Peano.Axiom.succ_ne_zero (.var 0)))

/-- The free-variable check rules out an invalid vacuous generalization. -/
theorem variable_is_free :
    0 ∈ ((.var 0 : Peano.Term).equal Peano.zero).freeVarFinset := by
  simp [Term.equal, Term.bdEqual, Peano.zero, BoundedFormula.freeVarFinset,
    Term.varFinsetLeft]

/-- Substitution through a binder is capture avoiding: replacing parameter 1
by variable 0 does not turn `forall x, x = parameter` into `forall x, x = x`. -/
theorem substitution_scope_control :
    ¬ (FOL.substAt (FOL.allAt 0
      ((.var 0 : Peano.Term).equal (.var 1))) 1 (.var 0)).Realize (fun _ => 0 : Nat → Nat) := by
  rw [FOL.realize_substAt, FOL.realize_allAt]
  intro h
  have h1 := h 1
  simp at h1

end PASoundness.Fixtures
