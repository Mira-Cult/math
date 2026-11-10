import PASoundness.PeanoFiniteComprehensionClosed
import PASoundness.PeanoAX8SingletonClosed

/-! A canonical-name PA singleton selector witness. Mapping the formula and
names to an arbitrary literal AX8 instance is a separate obligation. -/
namespace PASoundness.PeanoAX8SingletonCanonical
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoFiniteComprehensionBase PeanoAX8SingletonCombine

/-- The output code satisfies both alias obligations, for any ψ fresh in the
fixed length and witness names 0, 2, and 3. Name 1 is its index and name 5
is the separately retained outer index. -/
theorem canonical_singleton (ψ : Peano.Formula)
    (hψ0 : 0 ∉ ψ.freeVarFinset) (hψ2 : 2 ∉ ψ.freeVarFinset)
    (hψ3 : 3 ∉ ψ.freeVarFinset) :
    FormulaProves (FOL.existsAt 3 (aliasConsequences ψ)) := by
  let φ := PeanoAX8SingletonSelector.selector ψ
  have hf0 : 0 ∉ φ.freeVarFinset := by
    have he : 0 ∉ ((.var 1 : Peano.Term).equal (.var 5)).freeVarFinset := by decide
    change 0 ∉ (((.var 1 : Peano.Term).equal (.var 5)).imp ψ.not).not.freeVarFinset
    simp [FirstOrder.Language.BoundedFormula.freeVarFinset, hψ0, he]
  have hf2 : 2 ∉ φ.freeVarFinset := by
    have he : 2 ∉ ((.var 1 : Peano.Term).equal (.var 5)).freeVarFinset := by decide
    change 2 ∉ (((.var 1 : Peano.Term).equal (.var 5)).imp ψ.not).not.freeVarFinset
    simp [FirstOrder.Language.BoundedFormula.freeVarFinset, hψ2, he]
  have hf3 : 3 ∉ φ.freeVarFinset := by
    have he : 3 ∉ ((.var 1 : Peano.Term).equal (.var 5)).freeVarFinset := by decide
    change 3 ∉ (((.var 1 : Peano.Term).equal (.var 5)).imp ψ.not).not.freeVarFinset
    simp [FirstOrder.Language.BoundedFormula.freeVarFinset, hψ3, he]
  exact .mp (PeanoAX8SingletonClosed.singleton_of_universal ψ hψ0 hψ2 hψ3)
    (PeanoFiniteComprehensionClosed.selector_total φ hf0 hf2 hf3)

end PASoundness.PeanoAX8SingletonCanonical

#print axioms PASoundness.PeanoAX8SingletonCanonical.canonical_singleton
