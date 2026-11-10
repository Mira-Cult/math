import PASoundness.PeanoAX8SingletonSelector
import PASoundness.PeanoAX8SelectorExtraction

/-! Conditional singleton-selector extraction with one shared output code.
This is an alias-case component, not a full literal AX8 derivation. -/
namespace PASoundness.PeanoAX8SingletonCombine
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoFiniteComprehensionBase

def aliasConsequences (ψ : Peano.Formula) : Peano.Formula :=
  (FOL.allAt 1 ((bitFormula (.var 3) (.var 1)).imp ψ)) ⊓
    ((FOL.substAt ψ 1 (.var 5)).imp (bitFormula (.var 3) (.var 5)))

/-- A bounded selector invariant yields one code satisfying both reduced
alias obligations: global output-to-ψ and the separate outer-index bit.
The selector must be fresh at witness names 2 and 3. -/
theorem singleton_solution (ψ : Peano.Formula)
    (hψ2 : 2 ∉ ψ.freeVarFinset) (hψ3 : 3 ∉ ψ.freeVarFinset) :
    FormulaProves ((invariant (PeanoAX8SingletonSelector.selector ψ) (.var 0)).imp
      ((less (.var 5) (.var 0)).imp (FOL.existsAt 3 (aliasConsequences ψ)))) := by
  let φ := PeanoAX8SingletonSelector.selector ψ
  let I := invariant φ (.var 0)
  let S := PeanoAX8SelectorExtraction.selectorBound φ
  let G := PeanoAX8SingletonSelector.globalRows ψ
  let C := aliasConsequences ψ
  let T := FOL.existsAt 3 C
  have hf2 : 2 ∉ φ.freeVarFinset := by
    have he : 2 ∉ ((.var 1 : Peano.Term).equal (.var 5)).freeVarFinset := by decide
    change 2 ∉ (((.var 1 : Peano.Term).equal (.var 5)).imp ψ.not).not.freeVarFinset
    simp [FirstOrder.Language.BoundedFormula.freeVarFinset, hψ2, he]
  have hf3 : 3 ∉ φ.freeVarFinset := by
    have he : 3 ∉ ((.var 1 : Peano.Term).equal (.var 5)).freeVarFinset := by decide
    change 3 ∉ (((.var 1 : Peano.Term).equal (.var 5)).imp ψ.not).not.freeVarFinset
    simp [FirstOrder.Language.BoundedFormula.freeVarFinset, hψ3, he]
  have hbody : FormulaProves (G.imp T) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have hg : FOL.Context Peano.Axiom [G] G := .head [] _
    have hfirst : FOL.Context Peano.Axiom [G]
        (FOL.allAt 1 ((bitFormula (.var 3) (.var 1)).imp ψ)) :=
      .mp (.closed (PeanoAX8SingletonSelector.output_implies_relation ψ)) hg
    have hsecond : FOL.Context Peano.Axiom [G]
        ((FOL.substAt ψ 1 (.var 5)).imp (bitFormula (.var 3) (.var 5))) :=
      .mp (.closed (PeanoAX8SingletonSelector.outer_relation_implies_bit ψ)) hg
    have hc : FOL.Context Peano.Axiom [G] C := FOL.Context.conjunctionIntro hfirst hsecond
    have hi : FormulaProves (C.imp T) := by
      simpa only [T, SyntaxTransport.substAt_self] using
        (FOL.Derivation.existsIntro (A := Peano.Axiom) C 3 (.var 3))
    exact .mp (.closed hi) hc
  have hf : 3 ∉ T.freeVarFinset := by
    simp [T, FOL.existsAt, SyntaxTransport.allAt_freeVars,
      FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset]
  have helim := PeanoBitPositionReduction.exists_elim 3 hf hbody
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let H := less (.var 5) (.var 0)
  let Γ := [H, I]
  have hi : FOL.Context Peano.Axiom Γ I := .hypothesis (by simp [Γ])
  have hh : FOL.Context Peano.Axiom Γ H := .head _ _
  have hs : FOL.Context Peano.Axiom Γ S :=
    .mp (.closed (PeanoAX8SingletonSelector.selector_bounded ψ)) hh
  have he : FOL.Context Peano.Axiom Γ (FOL.existsAt 3 G) := by
    have h : FOL.Context Peano.Axiom Γ (PeanoAX8SelectorExtraction.globalExists φ) :=
      .mp (.mp (.closed (PeanoAX8SelectorExtraction.invariant_global φ hf2 hf3)) hi) hs
    simpa only [PeanoAX8SelectorExtraction.globalExists,
      PeanoAX8SelectorExtraction.globalRows, PeanoAX8SingletonSelector.globalRows, φ, G] using h
  exact .mp (.closed helim) he

end PASoundness.PeanoAX8SingletonCombine

#print axioms PASoundness.PeanoAX8SingletonCombine.singleton_solution
