import PASoundness.PeanoBitLowerPreservationAll
import PASoundness.PeanoPowerTotalityClosed
import PASoundness.PeanoBetaCRTAlpha

/-! Below the selected endpoint, adding the endpoint power preserves both
directions of membership for the canonical finite-comprehension names. -/
namespace PASoundness.PeanoFiniteComprehensionLower
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

private theorem power_exists_at_index : FormulaProves
    (FOL.existsAt 6 (pow2 (.var 1) (.var 6))) := by
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom)
      (.allElim PeanoPowerTotality.existsPower 0 (.var 1)))
    PeanoPowerTotalityClosed.power_total
  have hs : FOL.substAt PeanoPowerTotality.existsPower 0 (.var 1) =
      FOL.existsAt 6 (pow2 (.var 1) (.var 6)) := by
    unfold PeanoPowerTotality.existsPower
    rw [PeanoBetaCRTAlpha.subst_var_existsAt _ 0 1 6 (by decide) (by decide)]
    simp [FOL.substAt, pow2_subst, FirstOrder.Language.Term.subst]
  simpa only [hs] using h

/-- PA proves both membership implications for the code `a+p` at any
index `i<n`, assuming a literal trace for `p=2^n`. Free variables 0,1,2,3
are respectively n,i,p,a; the intermediate power witness is eliminated. -/
theorem lower_preserved_add_right : FormulaProves
    ((pow2 (.var 0) (.var 2)).imp
      ((less (.var 1) (.var 0)).imp
        (((bitFormula (.var 3) (.var 1)).imp
            (bitFormula (add (.var 3) (.var 2)) (.var 1))) ⊓
          ((bitFormula (add (.var 3) (.var 2)) (.var 1)).imp
            (bitFormula (.var 3) (.var 1)))))) := by
  let Q := pow2 (.var 1) (.var 6)
  let P := pow2 (.var 0) (.var 2)
  let L := less (.var 1) (.var 0)
  let B := bitFormula (.var 3) (.var 1)
  let B' := bitFormula (add (.var 3) (.var 2)) (.var 1)
  let G := P.imp (L.imp ((B.imp B') ⊓ (B'.imp B)))
  have hbody : FormulaProves (Q.imp G) := by
    simpa only [Q, G, P, L, B, B'] using
      PeanoBitLowerPreservationAll.lower_bits_preserved_all
        (.var 0) (.var 1) (.var 6) (.var 3) (.var 2)
  have hf : 6 ∉ G.freeVarFinset := by decide
  have h := PeanoBitPositionReduction.exists_elim 6 hf hbody
  exact .mp h power_exists_at_index

end PASoundness.PeanoFiniteComprehensionLower

#print axioms PASoundness.PeanoFiniteComprehensionLower.lower_preserved_add_right
