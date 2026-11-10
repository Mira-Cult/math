import PASoundness.PeanoBetaCRTAlpha

/-! Capture-safe renaming of a named universal binder for the AX8 transport.
This is a syntactic derivation rule, not a comprehension theorem. -/
namespace PASoundness.PeanoAX8AllAlpha
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic

/-- Changing a universal binder from `x` to `y` is derivable in PA whenever
`y` is fresh in the body. The replacement is the actual capture-safe
substitution, not textual replacement under nested binders. -/
theorem all_alpha_forward (φ : Peano.Formula) (x y : Nat)
    (_hxy : x ≠ y) (hy : y ∉ φ.freeVarFinset) :
    FormulaProves ((FOL.allAt x φ).imp (FOL.allAt y (FOL.substAt φ x (.var y)))) := by
  let H := FOL.allAt x φ
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.generalize y
  · intro ψ hψ
    simp only [List.mem_singleton] at hψ
    subst ψ
    simp [SyntaxTransport.allAt_freeVars, hy]
  · exact FOL.Context.allElim (FOL.Context.head [] H) (.var y)

/-- The reverse direction uses the same freshness side condition. -/
theorem all_alpha_backward (φ : Peano.Formula) (x y : Nat)
    (hxy : x ≠ y) (hy : y ∉ φ.freeVarFinset) :
    FormulaProves ((FOL.allAt y (FOL.substAt φ x (.var y))).imp (FOL.allAt x φ)) := by
  have hx : x ∉ (FOL.substAt φ x (.var y)).freeVarFinset :=
    PeanoBetaCRTAlpha.subst_rename_fresh φ x y hxy
  have h := all_alpha_forward (FOL.substAt φ x (.var y)) y x (Ne.symm hxy) hx
  rw [PeanoBetaCRTAlpha.subst_roundtrip φ x y hxy hy] at h
  exact h

end PASoundness.PeanoAX8AllAlpha

#print axioms PASoundness.PeanoAX8AllAlpha.all_alpha_forward
#print axioms PASoundness.PeanoAX8AllAlpha.all_alpha_backward
