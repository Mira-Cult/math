import PASoundness.PeanoOrderIrreflexive

/-! An exact object-level witness reduction for the bit-position obligation.
The arithmetic witness implication is an explicit, unresolved premise. -/
namespace PASoundness.PeanoBitPositionReduction
open FirstOrder FirstOrder.Language
open PASoundness.FOL PASoundness.Peano PASoundness.CompactArithmetic

/-- Eliminate an existential from a closed finite Hilbert derivation. The
eigenvariable must be absent from the actual conclusion's free-variable set. -/
theorem exists_elim {L : Language} {A : FOL.Formula L → Prop}
    (x : Nat) {φ ψ : FOL.Formula L} (hx : x ∉ ψ.freeVarFinset)
    (h : FOL.Derivation A (φ.imp ψ)) :
    FOL.Derivation A ((FOL.existsAt x φ).imp ψ) := by
  have hn : x ∉ ψ.not.freeVarFinset := by
    simpa only [BoundedFormula.not, BoundedFormula.freeVarFinset, Finset.union_empty] using hx
  have h₁ : FOL.Derivation A (ψ.not.imp (FOL.allAt x φ.not)) :=
    FOL.Derivation.compose (.logical (.vacuous ψ.not x hn))
      (FOL.Derivation.allCongr x (FOL.Derivation.contrapose h))
  exact FOL.Derivation.compose (FOL.Derivation.contrapose h₁)
    (.logical (.classical ψ))

def a : Peano.Term := .var 0
def x : Peano.Term := .var 1
def p : Peano.Term := .var 2
def q : Peano.Term := .var 3
def r : Peano.Term := .var 4
def goal : Peano.Formula := less x a
def power : Peano.Formula := pow2 x p
def row : Peano.Formula :=
  (a.equal (add (add (mul q (add p p)) p) r)) ⊓ (less r p)
def witnessBound : Peano.Formula := row.imp (power.imp goal)

/-- The remaining witness bound follows from two separate object-level PA
implications: power-trace growth and order propagation through the exact
quotient/remainder equation. Neither implication is established here. -/
theorem witness_bound_of_components
    (hpower : Peano.FormulaProves (power.imp (less x p)))
    (hshape : Peano.FormulaProves
      ((a.equal (add (add (mul q (add p p)) p) r)).imp
        ((less x p).imp goal))) :
    Peano.FormulaProves witnessBound := by
  change Peano.FormulaProves (row.imp (power.imp goal))
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hrow : FOL.Context Peano.Axiom [power, row] row :=
    FOL.Context.under (FOL.Context.head [] row) power
  have heq := FOL.Context.conjunctionLeft hrow
  have hp : FOL.Context Peano.Axiom [power, row] (less x p) :=
    .mp (.closed hpower) (FOL.Context.head [row] power)
  exact .mp (.mp (.closed hshape) heq) hp

/-- Eliminate the three literal bit-template witnesses from the displayed
object-level arithmetic implication. The implication is a premise; this
theorem does not assert PA derives the power and order inequalities yet. -/
theorem bit_template_of_witness_bound
    (hrow : Peano.FormulaProves witnessBound) :
    Peano.FormulaProves (bitTemplate.imp goal) := by
  change Peano.FormulaProves (row.imp (power.imp goal)) at hrow
  have h4 : 4 ∉ (power.imp goal).freeVarFinset := by decide
  have h3 : 3 ∉ (power.imp goal).freeVarFinset := by decide
  have h2 : 2 ∉ goal.freeVarFinset := by decide
  have e4 := exists_elim 4 h4 hrow
  have e3 := exists_elim 3 h3 e4
  have hbody : Peano.FormulaProves
      ((power ⊓ FOL.existsAt 3 (FOL.existsAt 4 row)).imp goal) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have hconj : FOL.Context Peano.Axiom
        [power ⊓ FOL.existsAt 3 (FOL.existsAt 4 row)]
        (power ⊓ FOL.existsAt 3 (FOL.existsAt 4 row)) := FOL.Context.head [] _
    exact .mp (.mp (.closed e3) (FOL.Context.conjunctionRight hconj))
      (FOL.Context.conjunctionLeft hconj)
  have h := exists_elim 2 h2 hbody
  simpa only [bitTemplate, CompactArithmetic.exAt, a, x, p, q, r, row, power, goal,
    CompactArithmetic.v, FOL.existsAt] using h

private theorem bitTemplate_as_bitFormula : bitFormula a x = bitTemplate := by
  unfold bitFormula
  calc
    bitTemplate.subst (fun y => if y = 0 then a else if y = 1 then x else zero) =
        bitTemplate.subst Term.var := by
      apply SyntaxTransport.formula_subst_agree
      intro y hy
      simp only [bitTemplate_freeVars, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> rfl
    _ = bitTemplate := SyntaxTransport.formula_subst_var _

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := by
  rfl

/-- The compact bit-position implication follows from the explicit arithmetic
witness premise above. This step performs only finite object-level logic and
capture-avoiding syntax substitutions. -/
theorem bit_position_of_witness_bound
    (hrow : Peano.FormulaProves witnessBound) :
    Peano.FormulaProves ((bitFormula a x).imp (less x a)) := by
  simpa only [bitTemplate_as_bitFormula, goal] using bit_template_of_witness_bound hrow

/-- The arithmetic witness premise suffices for the exact translated-bottom
obligation, using PA's proved irreflexivity of the compact strict order. -/
theorem translated_bottom_of_witness_bound
    (hrow : Peano.FormulaProves witnessBound) :
    Peano.FormulaProves (CompactLogicalTransport.interpreted 1).not := by
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom)
      (.allElim ((bitFormula a x).imp (less x a)) 1 (.var 0)))
    (.generalize 1 (bit_position_of_witness_bound hrow))
  apply PeanoOrderIrreflexive.translated_bottom_of_bit_position
  simpa [FOL.substAt, subst_imp, bitFormula_subst, less_subst,
    a, x, FirstOrder.Language.Term.subst] using h

end PASoundness.PeanoBitPositionReduction
