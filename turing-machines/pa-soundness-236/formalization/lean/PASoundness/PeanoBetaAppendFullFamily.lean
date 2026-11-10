import PASoundness.PeanoBetaAppendEndFamily
import PASoundness.PeanoBetaAppendFamilyMerge

/-! A supplied append recoding preserves all doubling transitions through n.
The old trace, recoding rows, and old endpoint are explicit premises. -/
namespace PASoundness.PeanoBetaAppendFullFamily
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoBetaAppendTraceFamily PeanoBetaAppendTransition

/-- The new code has a doubling pair at every index `i < S n`. -/
def fullFamily : Peano.Formula := FOL.allAt 2
  ((less (.var 2) (succ (.var 0))).imp
    (FOL.existsAt 20 (FOL.existsAt 21 newBody)))

/-- The old family below n, a recoding row family, and the old endpoint
jointly yield the full new family below `S n`, including the new transition
at n. Both witnesses in each transition are retained. -/
theorem full_family_preserved : FormulaProves
    (oldFamily.imp (recodedRows.imp
      ((beta (.var 4) (.var 5) (.var 0) (.var 6)).imp fullFamily))) := by
  let E := beta (.var 4) (.var 5) (.var 0) (.var 6)
  let F := FOL.existsAt 20 (FOL.existsAt 21 newBody)
  let Γ := [E, recodedRows, oldFamily]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have he : FOL.Context Peano.Axiom Γ E := FOL.Context.head _ _
  have hr : FOL.Context Peano.Axiom Γ recodedRows := .hypothesis (by simp [Γ])
  have ho : FOL.Context Peano.Axiom Γ oldFamily := .hypothesis (by simp [Γ])
  have hs : FOL.Context Peano.Axiom Γ newFamily :=
    .mp (.mp (.closed family_preserved) ho) hr
  have hb : FOL.Context Peano.Axiom Γ (FOL.substAt F 2 (.var 0)) :=
    .mp (.mp (.closed PeanoBetaAppendEndFamily.endpoint_family) hr) he
  exact .mp (.mp (.closed (PeanoBetaAppendFamilyMerge.merge_family F)) hs) hb

end PASoundness.PeanoBetaAppendFullFamily

#print axioms PASoundness.PeanoBetaAppendFullFamily.full_family_preserved
