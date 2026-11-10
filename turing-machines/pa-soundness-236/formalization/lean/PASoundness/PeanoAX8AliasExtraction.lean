import PASoundness.PeanoBitAlias
import PASoundness.PeanoBitPositionReduction

/-! A PA reduction of the exact AX8 formula in the alias case `a = b`.

Only the quantified implication with antecedent `bit(b,b)` is removed. The
separate occurrence at the outer value of `b` remains literally in the
reduced formula. This is not a derivation of the reduced formula or of AX8.
-/
namespace PASoundness.PeanoAX8AliasExtraction
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open CompactLogicalTransport

/-- The residual condition retains both a universally quantified output-to-
predicate implication and the distinct outer-b membership obligation. If
`c = b`, the enclosing existential also binds that outer occurrence. -/
def aliasReduced (b c : Nat) : Peano.Formula :=
  FOL.existsAt c
    ((FOL.allAt b ((bitFormula (.var c) (.var b)).imp (interpreted c))) ⊓
      ((interpreted c).imp (bitFormula (.var c) (.var b))))

private theorem all_case_add (b c : Nat) : FormulaProves
    ((FOL.allAt b ((bitFormula (.var c) (.var b)).imp (interpreted c))).imp
      (FOL.allAt b
        (((bitFormula (.var b) (.var b)).imp
          ((interpreted c).imp (bitFormula (.var c) (.var b)))) ⊓
         ((bitFormula (.var c) (.var b)).imp (interpreted c))))) := by
  let P := (bitFormula (.var c) (.var b)).imp (interpreted c)
  let Q := (bitFormula (.var b) (.var b)).imp
    ((interpreted c).imp (bitFormula (.var c) (.var b)))
  have h : FormulaProves (P.imp (Q ⊓ P)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have hp : FOL.Context Peano.Axiom [P] P := FOL.Context.head [] P
    have hq : FOL.Context Peano.Axiom [P] Q :=
      .closed (FOL.Derivation.compose (PeanoBitAlias.bit_irreflexive (.var b))
        (FOL.Derivation.explosion _))
    exact FOL.Context.conjunctionIntro hq hp
  exact FOL.Derivation.allCongr b h

private theorem all_case_drop (b c : Nat) : FormulaProves
    ((FOL.allAt b
        (((bitFormula (.var b) (.var b)).imp
          ((interpreted c).imp (bitFormula (.var c) (.var b)))) ⊓
         ((bitFormula (.var c) (.var b)).imp (interpreted c)))).imp
      (FOL.allAt b ((bitFormula (.var c) (.var b)).imp (interpreted c)))) := by
  let P := (bitFormula (.var c) (.var b)).imp (interpreted c)
  let Q := (bitFormula (.var b) (.var b)).imp
    ((interpreted c).imp (bitFormula (.var c) (.var b)))
  have h : FormulaProves ((Q ⊓ P).imp P) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    exact FOL.Context.conjunctionRight (FOL.Context.head [] _)
  exact FOL.Derivation.allCongr b h

private theorem exists_congr_forward (c : Nat) (P Q : Peano.Formula)
    (h : FormulaProves (P.imp Q)) :
    FormulaProves ((FOL.existsAt c P).imp (FOL.existsAt c Q)) := by
  let T := FOL.existsAt c Q
  have hi : FormulaProves (Q.imp T) := by
    simpa only [T, SyntaxTransport.substAt_self] using
      (FOL.Derivation.existsIntro (A := Peano.Axiom) Q c (.var c))
  have ht : FormulaProves (P.imp T) := FOL.Derivation.compose h hi
  have hf : c ∉ T.freeVarFinset := by
    simp [T, FOL.existsAt, SyntaxTransport.allAt_freeVars,
      FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset]
  exact PeanoBitPositionReduction.exists_elim c hf ht

/-- The exact alias AX8 formula follows from the displayed residual selector
condition. The same existential witness is retained, and no freshness or
noncollision hypothesis is needed for this syntactic reduction. -/
theorem alias_of_reduced (b c : Nat) : FormulaProves
    ((aliasReduced b c).imp (comprehensionFormula b b c)) := by
  let P := FOL.allAt b ((bitFormula (.var c) (.var b)).imp (interpreted c))
  let Q := FOL.allAt b
    (((bitFormula (.var b) (.var b)).imp
      ((interpreted c).imp (bitFormula (.var c) (.var b)))) ⊓
     ((bitFormula (.var c) (.var b)).imp (interpreted c)))
  let R := (interpreted c).imp (bitFormula (.var c) (.var b))
  have hbody : FormulaProves ((P ⊓ R).imp (Q ⊓ R)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have h : FOL.Context Peano.Axiom [P ⊓ R] (P ⊓ R) := FOL.Context.head [] _
    exact FOL.Context.conjunctionIntro
      (.mp (.closed (all_case_add b c)) (FOL.Context.conjunctionLeft h))
      (FOL.Context.conjunctionRight h)
  rw [PeanoBitAlias.comprehension_alias_syntax]
  simpa only [aliasReduced, P, Q, R] using
    exists_congr_forward c (P ⊓ R) (Q ⊓ R) hbody

/-- Conversely, the literal alias formula supplies the same residual
condition, retaining its existential witness and outer-b occurrence. -/
theorem reduced_of_alias (b c : Nat) : FormulaProves
    ((comprehensionFormula b b c).imp (aliasReduced b c)) := by
  let P := FOL.allAt b ((bitFormula (.var c) (.var b)).imp (interpreted c))
  let Q := FOL.allAt b
    (((bitFormula (.var b) (.var b)).imp
      ((interpreted c).imp (bitFormula (.var c) (.var b)))) ⊓
     ((bitFormula (.var c) (.var b)).imp (interpreted c)))
  let R := (interpreted c).imp (bitFormula (.var c) (.var b))
  have hbody : FormulaProves ((Q ⊓ R).imp (P ⊓ R)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have h : FOL.Context Peano.Axiom [Q ⊓ R] (Q ⊓ R) := FOL.Context.head [] _
    exact FOL.Context.conjunctionIntro
      (.mp (.closed (all_case_drop b c)) (FOL.Context.conjunctionLeft h))
      (FOL.Context.conjunctionRight h)
  rw [PeanoBitAlias.comprehension_alias_syntax]
  simpa only [aliasReduced, P, Q, R] using
    exists_congr_forward c (Q ⊓ R) (P ⊓ R) hbody

end PASoundness.PeanoAX8AliasExtraction

#print axioms PASoundness.PeanoAX8AliasExtraction.alias_of_reduced
#print axioms PASoundness.PeanoAX8AliasExtraction.reduced_of_alias
