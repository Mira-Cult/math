import PASoundness.PeanoFiniteComprehensionBase
import PASoundness.PeanoPowerFiniteSupport

/-! Extend an explicitly bounded selector to all indices inside PA. This is a
conditional component of AX8 extraction; the selector's boundedness remains
an explicit premise and no particular literal AX8 instance is asserted. -/
namespace PASoundness.PeanoAX8SelectorExtraction
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoFiniteComprehensionBase

/-- The intended selector has no true instances at or above the length. -/
def selectorBound (φ : Peano.Formula) : Peano.Formula :=
  FOL.allAt 1 (φ.imp (less (.var 1) (.var 0)))

/-- Global equality of the selected relation and the selected output bits. -/
def globalRows (φ : Peano.Formula) : Peano.Formula :=
  FOL.allAt 1 (((bitFormula (.var 3) (.var 1)).imp φ) ⊓
    (φ.imp (bitFormula (.var 3) (.var 1))))

/-- If a concrete code is below the length's literal power, PA extends its
bounded row agreement to all positions when the selector itself is bounded.
All variables beyond the bound index 1 remain parameters of the formula. -/
theorem global_of_bounded (φ : Peano.Formula) : FormulaProves
    ((pow2 (.var 0) (.var 2)).imp
      ((less (.var 3) (.var 2)).imp
        ((rows φ (.var 0) (.var 3)).imp
          ((selectorBound φ).imp (globalRows φ))))) := by
  let P := pow2 (.var 0) (.var 2)
  let C := less (.var 3) (.var 2)
  let R := rows φ (.var 0) (.var 3)
  let S := selectorBound φ
  let L := less (.var 1) (.var 0)
  let B := bitFormula (.var 3) (.var 1)
  let T := (B.imp φ) ⊓ (φ.imp B)
  let Γ := [S, R, C, P]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  change FOL.Context Peano.Axiom Γ (FOL.allAt 1 T)
  apply FOL.Context.generalize 1
  · intro ψ hψ
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hψ
    rcases hψ with rfl | rfl | rfl | rfl
    · simp [S, selectorBound, SyntaxTransport.allAt_freeVars]
    · simp [R, rows, SyntaxTransport.allAt_freeVars]
    · decide
    · decide
  have hs : FOL.Context Peano.Axiom Γ S := .head _ _
  have hr : FOL.Context Peano.Axiom Γ R := .hypothesis (by simp [Γ])
  have hc : FOL.Context Peano.Axiom Γ C := .hypothesis (by simp [Γ])
  have hp : FOL.Context Peano.Axiom Γ P := .hypothesis (by simp [Γ])
  have hrows : FOL.Context Peano.Axiom Γ (L.imp T) := FOL.Context.allSelf hr
  have hbound : FOL.Context Peano.Axiom Γ (φ.imp L) := FOL.Context.allSelf hs
  have hsupport : FOL.Context Peano.Axiom Γ (L.not.imp B.not) :=
    .mp (.mp (.closed PeanoPowerFiniteSupport.finite_support_vars) hp) hc
  have hforward : FOL.Context Peano.Axiom Γ (B.imp φ) := by
    apply FOL.Context.deduction
    have hb : FOL.Context Peano.Axiom (B :: Γ) B := .head _ _
    have hl : FOL.Context Peano.Axiom (B :: Γ) L := by
      apply FOL.Context.dne
      apply FOL.Context.deduction
      exact .mp (.mp (.under (.under hsupport _) _) (.head _ _)) (.under hb _)
    have ht : FOL.Context Peano.Axiom (B :: Γ) T := .mp (.under hrows B) hl
    exact .mp (FOL.Context.conjunctionLeft ht) hb
  have hback : FOL.Context Peano.Axiom Γ (φ.imp B) := by
    apply FOL.Context.deduction
    have hφ : FOL.Context Peano.Axiom (φ :: Γ) φ := .head _ _
    have hl : FOL.Context Peano.Axiom (φ :: Γ) L := .mp (.under hbound φ) hφ
    have ht : FOL.Context Peano.Axiom (φ :: Γ) T := .mp (.under hrows φ) hl
    exact .mp (FOL.Context.conjunctionRight ht) hφ
  exact FOL.Context.conjunctionIntro hforward hback

/-- A code satisfying the global selector relation. -/
def globalExists (φ : Peano.Formula) : Peano.Formula := FOL.existsAt 3 (globalRows φ)

/-- Eliminate the invariant's power witness and retain its very same code.
The selector must not mention either existential witness name freely; all
other parameters, including its index at name 1, remain available. -/
theorem invariant_global (φ : Peano.Formula)
    (hφ2 : 2 ∉ φ.freeVarFinset) (hφ3 : 3 ∉ φ.freeVarFinset) :
    FormulaProves ((invariant φ (.var 0)).imp
      ((selectorBound φ).imp (globalExists φ))) := by
  let M := matrix φ (.var 0)
  let S := selectorBound φ
  let E := globalExists φ
  have hbody : FormulaProves (M.imp (S.imp E)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    let Γ := [S, M]
    have hm : FOL.Context Peano.Axiom Γ M := .hypothesis (by simp [Γ])
    have hs : FOL.Context Peano.Axiom Γ S := .head _ _
    have hp : FOL.Context Peano.Axiom Γ (pow2 (.var 0) (.var 2)) :=
      FOL.Context.conjunctionLeft hm
    have htail := FOL.Context.conjunctionRight hm
    have hc : FOL.Context Peano.Axiom Γ (less (.var 3) (.var 2)) :=
      FOL.Context.conjunctionLeft htail
    have hr : FOL.Context Peano.Axiom Γ (rows φ (.var 0) (.var 3)) :=
      FOL.Context.conjunctionRight htail
    have hg : FOL.Context Peano.Axiom Γ (globalRows φ) :=
      .mp (.mp (.mp (.mp (.closed (global_of_bounded φ)) hp) hc) hr) hs
    have hi : FormulaProves ((globalRows φ).imp E) := by
      simpa only [E, globalExists, SyntaxTransport.substAt_self] using
        (FOL.Derivation.existsIntro (A := Peano.Axiom) (globalRows φ) 3 (.var 3))
    exact .mp (.closed hi) hg
  have h3 : 3 ∉ (S.imp E).freeVarFinset := by
    have hl : 3 ∉ (less (.var 1) (.var 0)).freeVarFinset := by decide
    simp [S, E, selectorBound, globalExists, FOL.existsAt, SyntaxTransport.allAt_freeVars,
      FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset,
      hφ3, hl]
  have h2 : 2 ∉ (S.imp E).freeVarFinset := by
    have hl : 2 ∉ (less (.var 1) (.var 0)).freeVarFinset := by decide
    have hb : 2 ∉ (bitFormula (.var 3) (.var 1)).freeVarFinset := by decide
    have ht : 2 ∉ (((bitFormula (.var 3) (.var 1)).imp φ) ⊓
        (φ.imp (bitFormula (.var 3) (.var 1)))).freeVarFinset := by
      change 2 ∉ (((bitFormula (.var 3) (.var 1)).imp φ).imp
        (φ.imp (bitFormula (.var 3) (.var 1))).not).not.freeVarFinset
      simp [FirstOrder.Language.BoundedFormula.freeVarFinset, hφ2, hb]
    simp [S, E, selectorBound, globalExists, globalRows, FOL.existsAt,
      SyntaxTransport.allAt_freeVars, FirstOrder.Language.BoundedFormula.not,
      FirstOrder.Language.BoundedFormula.freeVarFinset, hφ2, hl, ht]
  have he3 := PeanoBitPositionReduction.exists_elim 3 h3 hbody
  have he2 := PeanoBitPositionReduction.exists_elim 2 h2 he3
  simpa only [invariant, M, S, E] using he2

end PASoundness.PeanoAX8SelectorExtraction

#print axioms PASoundness.PeanoAX8SelectorExtraction.global_of_bounded
#print axioms PASoundness.PeanoAX8SelectorExtraction.invariant_global
