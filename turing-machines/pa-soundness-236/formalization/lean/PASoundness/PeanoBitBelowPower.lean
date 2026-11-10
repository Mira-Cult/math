import PASoundness.PeanoBitWitnessElim
import PASoundness.PeanoPowerUnique
import PASoundness.PeanoBitBelowOrder

/-! A code below a literal power has no bit at that power's index.
All reasoning is a derivation in PA, including uniqueness of the power. -/
namespace PASoundness.PeanoBitBelowPower
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoBitPositionReduction

/-- Variables 0, 1, and 5 denote the code, index, and independently supplied
power. The power existential in the bit formula is eliminated using 2,3,4. -/
theorem below_excludes_bit_vars : FormulaProves
    ((pow2 (.var 1) (.var 5)).imp
      ((less (.var 0) (.var 5)).imp (bitFormula (.var 0) (.var 1)).not)) := by
  let K := pow2 (.var 1) (.var 5)
  let L := less (.var 0) (.var 5)
  let G := K.imp L.not
  have hrow : FormulaProves (row.imp (power.imp G)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    let Γ := [L, K, power, row]
    have hr : FOL.Context Peano.Axiom Γ row := .hypothesis (by simp [Γ])
    have hp : FOL.Context Peano.Axiom Γ power := .hypothesis (by simp [Γ])
    have hk : FOL.Context Peano.Axiom Γ K := .hypothesis (by simp [Γ])
    have hl : FOL.Context Peano.Axiom Γ L := FOL.Context.head _ _
    have he : FOL.Context Peano.Axiom Γ ((.var 2 : Peano.Term).equal (.var 5)) :=
      .mp (.mp (.closed (PeanoPowerUnique.power_unique (.var 1) (.var 2) (.var 5))) hp) hk
    have hl' : FOL.Context Peano.Axiom Γ (less (.var 0) (.var 2)) :=
      .mp (.mp (.closed (PeanoMultiplyQuotientStep.less_right_congr
        (.var 0) (.var 5) (.var 2))) (FOL.Context.eqSymm he)) hl
    have hn : FOL.Context Peano.Axiom Γ (less (.var 0) (.var 2)).not :=
      .mp (.closed (PeanoBitBelowOrder.row_not_below (.var 0) (.var 2) (.var 3) (.var 4)))
        (FOL.Context.conjunctionLeft hr)
    exact .mp hn hl'
  have hf2 : 2 ∉ G.freeVarFinset := by decide
  have hf3 : 3 ∉ G.freeVarFinset := by decide
  have hf4 : 4 ∉ G.freeVarFinset := by decide
  have h := PeanoBitWitnessElim.bit_elim G hf2 hf3 hf4 hrow
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let Γ := [bitFormula (.var 0) (.var 1), L, K]
  have hb : FOL.Context Peano.Axiom Γ (bitFormula (.var 0) (.var 1)) := FOL.Context.head _ _
  have hl : FOL.Context Peano.Axiom Γ L := .hypothesis (by simp [Γ])
  have hk : FOL.Context Peano.Axiom Γ K := .hypothesis (by simp [Γ])
  exact .mp (.mp (.mp (.closed h) hb) hk) hl

end PASoundness.PeanoBitBelowPower

#print axioms PASoundness.PeanoBitBelowPower.below_excludes_bit_vars
