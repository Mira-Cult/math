import PASoundness.PeanoFiniteComprehensionBase

/-! Transport bounded selector rows along a bounded bit equivalence. -/
namespace PASoundness.PeanoFiniteCompRowsTransport
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoFiniteComprehensionBase

/-- Below the bound, old and new codes have the same bit in both directions.
Name 1 is bound in the whole displayed body, including occurrences in k, a,
or b. To use those terms as fixed parameters, they must be fresh for name 1. -/
def sameRows (k a b : Peano.Term) : Peano.Formula :=
  FOL.allAt 1 ((less (.var 1) k).imp
    (((bitFormula a (.var 1)).imp (bitFormula b (.var 1))) ⊓
      ((bitFormula b (.var 1)).imp (bitFormula a (.var 1)))))

/-- PA transports a bounded filtering family along an explicitly supplied
bounded equivalence. No variable-freshness condition is needed for the proof:
both premises bind 1. If k, a, or b contains 1, its occurrences are bound
by these quantifiers rather than treated as fixed parameters. -/
theorem rows_transport (φ : Peano.Formula) (k a b : Peano.Term) : FormulaProves
    ((rows φ k a).imp ((sameRows k a b).imp (rows φ k b))) := by
  let L := less (.var 1) k
  let A := bitFormula a (.var 1)
  let B := bitFormula b (.var 1)
  let R := rows φ k a
  let S := sameRows k a b
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  change FOL.Context Peano.Axiom [S,R]
    (FOL.allAt 1 (L.imp ((B.imp φ) ⊓ (φ.imp B))))
  apply FOL.Context.generalize 1
  · intro ψ hψ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hψ
    rcases hψ with rfl | rfl
    · simp [S, sameRows, SyntaxTransport.allAt_freeVars]
    · simp [R, rows, SyntaxTransport.allAt_freeVars]
  apply FOL.Context.deduction
  let Γ := [L,S,R]
  have hl : FOL.Context Peano.Axiom Γ L := .head _ _
  have hs : FOL.Context Peano.Axiom Γ S := .hypothesis (by simp [Γ])
  have hr : FOL.Context Peano.Axiom Γ R := .hypothesis (by simp [Γ])
  have hsame : FOL.Context Peano.Axiom Γ ((A.imp B) ⊓ (B.imp A)) :=
    .mp (FOL.Context.allSelf hs) hl
  have hrow : FOL.Context Peano.Axiom Γ ((A.imp φ) ⊓ (φ.imp A)) :=
    .mp (FOL.Context.allSelf hr) hl
  have hforward : FOL.Context Peano.Axiom Γ (B.imp φ) := by
    apply FOL.Context.deduction
    have ha : FOL.Context Peano.Axiom (B :: Γ) A :=
      .mp (FOL.Context.under (FOL.Context.conjunctionRight hsame) B) (FOL.Context.head Γ B)
    exact .mp (FOL.Context.under (FOL.Context.conjunctionLeft hrow) B) ha
  have hreverse : FOL.Context Peano.Axiom Γ (φ.imp B) := by
    apply FOL.Context.deduction
    have ha : FOL.Context Peano.Axiom (φ :: Γ) A :=
      .mp (FOL.Context.under (FOL.Context.conjunctionRight hrow) φ) (FOL.Context.head Γ φ)
    exact .mp (FOL.Context.under (FOL.Context.conjunctionLeft hsame) φ) ha
  exact FOL.Context.conjunctionIntro hforward hreverse

end PASoundness.PeanoFiniteCompRowsTransport

#print axioms PASoundness.PeanoFiniteCompRowsTransport.rows_transport
