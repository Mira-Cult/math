import PASoundness.PeanoPowerDivisibilityCore
import PASoundness.PeanoPowerDivisibilityInstantiate
import PASoundness.PeanoPowerPredecessorSix

/-! Eliminate the predecessor witness in the power-divisibility step. -/
namespace PASoundness.PeanoPowerDivisibilitySuccessorOpen
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoDivisibility
open PeanoPowerDivisibilityInduction PeanoPowerPredecessorSix

/-- PA derives the open successor case from the induction family, using an
existential predecessor of the larger power and eliminating that witness. -/
theorem successor_open : FormulaProves (family.imp (body (succ (.var 0)))) := by
  let I : Peano.Term := .var 1
  let N : Peano.Term := .var 0
  let U : Peano.Term := .var 2
  let R : Peano.Term := .var 8
  let P : Peano.Term := .var 6
  let HU := pow2 I U
  let HP := pow2 (succ N) P
  let HL := less I (succ N)
  let D := divides (add U U) P
  let W := predecessorRow R
  let T := family.imp (HU.imp (HL.imp D))
  have hlocal : FormulaProves (W.imp T) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    let Γ := [HL, HU, family, W]
    have hw : FOL.Context Peano.Axiom Γ W := .hypothesis (by simp [Γ])
    have hf : FOL.Context Peano.Axiom Γ family := .hypothesis (by simp [Γ])
    have hu : FOL.Context Peano.Axiom Γ HU := .hypothesis (by simp [Γ])
    have hl : FOL.Context Peano.Axiom Γ HL := .head _ _
    have hr : FOL.Context Peano.Axiom Γ (pow2 N R) := FOL.Context.conjunctionLeft hw
    have he : FOL.Context Peano.Axiom Γ (P.equal (add R R)) := FOL.Context.conjunctionRight hw
    exact .mp (.mp (.mp (.mp (.mp
      (.closed (PeanoPowerDivisibilityCore.successor_from_predecessor
        PeanoPowerDivisibilityInstantiate.predecessor_instance)) hf) hu) hr) he) hl
  have hfresh : 8 ∉ T.freeVarFinset := by decide
  have helim := PeanoBitPositionReduction.exists_elim 8 hfresh hlocal
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let Γ := [HL, HP, HU, family]
  have hf : FOL.Context Peano.Axiom Γ family := .hypothesis (by simp [Γ])
  have hu : FOL.Context Peano.Axiom Γ HU := .hypothesis (by simp [Γ])
  have hp : FOL.Context Peano.Axiom Γ HP := .hypothesis (by simp [Γ])
  have hl : FOL.Context Peano.Axiom Γ HL := .head _ _
  have hex : FOL.Context Peano.Axiom Γ (FOL.existsAt 8 W) :=
    .mp (.closed PeanoPowerPredecessorSix.predecessor_six_eight) hp
  exact .mp (.mp (.mp (.mp (.closed helim) hex) hf) hu) hl

end PASoundness.PeanoPowerDivisibilitySuccessorOpen

#print axioms PASoundness.PeanoPowerDivisibilitySuccessorOpen.successor_open
