import PASoundness.PeanoPowerTransition

/-! The exact literal power formula with witness names suited to append
recoding. No new power trace or existence theorem is asserted. -/
namespace PASoundness.PeanoPowerOldUnpack
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

/-- A single doubling step for the old code and parameter. -/
def oldStep : Peano.Formula :=
  (beta (.var 4) (.var 5) (.var 2) (.var 20)) ⊓
    ((beta (.var 4) (.var 5) (succ (.var 2)) (.var 21)) ⊓
      ((.var 21 : Peano.Term).equal (add (.var 20) (.var 20))))

/-- All old-code doubling steps strictly below the endpoint name 0. -/
def oldFamily : Peano.Formula := FOL.allAt 2
  ((less (.var 2) (.var 0)).imp (FOL.existsAt 20 (FOL.existsAt 21 oldStep)))

/-- Initial row, endpoint row, and the bounded transition family for the
same old code 4 and parameter 5. -/
def oldMatrix : Peano.Formula :=
  (beta (.var 4) (.var 5) zero (succ zero)) ⊓
    ((beta (.var 4) (.var 5) (.var 0) (.var 6)) ⊓ oldFamily)

def unpackedPower : Peano.Formula := FOL.existsAt 4 (FOL.existsAt 5 oldMatrix)

/- The displayed names are an exact presentation of the literal formula:
named binders are translated to the same bound-variable syntax. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem literal_syntax : pow2 (.var 0) (.var 6) = unpackedPower := by
  simp [pow2, pow2Template, unpackedPower, oldMatrix, oldFamily, oldStep,
    FOL.existsAt, FOL.allAt, beta, betaTemplate, less, lessTemplate, modulus, exAt, v,
    Peano.add, Peano.mul, Peano.succ, Peano.zero, FirstOrder.Language.Term.equal,
    FirstOrder.Language.Term.bdEqual, FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux, Min.min]
  repeat' first
    | rfl
    | constructor
    | (congr 1; funext i; fin_cases i <;>
        dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])
  all_goals try simp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
  all_goals try
    (congr 1; funext i; fin_cases i; congr 1; funext j; fin_cases j <;>
      dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst] <;>
      first | rfl | (congr 1; funext k; fin_cases k; rfl))
  all_goals try (congr 1; funext i; exact Fin.elim0 i)
  all_goals try (congr 1; funext i; fin_cases i)
  all_goals try (congr 1; funext i; fin_cases i)
  all_goals try simp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst, Fin.elim0]
  all_goals try (congr 1; funext i; fin_cases i)
  all_goals try (congr 1; funext i; fin_cases i)

/-- PA may unpack a literal power trace into the same existential witnesses,
with no semantic interpretation or auxiliary derivability premise. -/
theorem old_power_unpack : FormulaProves ((pow2 (.var 0) (.var 6)).imp unpackedPower) := by
  rw [literal_syntax]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  exact FOL.Context.head [] unpackedPower

end PASoundness.PeanoPowerOldUnpack

#print axioms PASoundness.PeanoPowerOldUnpack.literal_syntax
#print axioms PASoundness.PeanoPowerOldUnpack.old_power_unpack
