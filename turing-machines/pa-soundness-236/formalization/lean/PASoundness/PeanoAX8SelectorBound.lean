import PASoundness.PeanoBitFiniteSupport

/-! A bounded selector for the non-alias AX8 extraction. This is an
object-level PA derivation and makes no claim of a full AX8 instance. -/
namespace PASoundness.PeanoAX8SelectorBound
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

/-- Input code 4 and outer distinguished position 5 are parameters; the
selector index is 1. The relation ψ may have arbitrary other free names. -/
def selector (ψ : Peano.Formula) : Peano.Formula :=
  ((bitFormula (.var 4) (.var 1)) ⊔ ((.var 1 : Peano.Term).equal (.var 5))) ⊓ ψ

private theorem or_elim {L : Language} {A : FOL.Formula L → Prop}
    {Γ : List (FOL.Formula L)} {φ ψ χ : FOL.Formula L}
    (h : FOL.Context A Γ (φ ⊔ ψ)) (hφ : FOL.Context A Γ (φ.imp χ))
    (hψ : FOL.Context A Γ (ψ.imp χ)) : FOL.Context A Γ χ := by
  apply FOL.Context.dne
  apply FOL.Context.deduction
  have hnφ : FOL.Context A (χ.not :: Γ) φ.not :=
    .mp (FOL.Context.under (FOL.Context.contrapose hφ) χ.not) (FOL.Context.head Γ χ.not)
  have hψ' : FOL.Context A (χ.not :: Γ) ψ :=
    .mp (FOL.Context.under h χ.not) hnφ
  exact .mp (FOL.Context.head Γ χ.not) (.mp (FOL.Context.under hψ χ.not) hψ')

/-- If both the input code and the distinguished outer index lie below name
0, then every selected index lies below name 0. The input is fixed here;
the literal a=b binder-alias case requires the separate alias reduction. -/
theorem selector_bounded (ψ : Peano.Formula) : FormulaProves
    ((less (.var 4) (.var 0)).imp ((less (.var 5) (.var 0)).imp
      (FOL.allAt 1 ((selector ψ).imp (less (.var 1) (.var 0)))))) := by
  let A := less (.var 4) (.var 0)
  let B := less (.var 5) (.var 0)
  let M := bitFormula (.var 4) (.var 1)
  let E := (.var 1 : Peano.Term).equal (.var 5)
  let L := less (.var 1) (.var 0)
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.generalize 1
  · intro χ hχ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
    rcases hχ with rfl | rfl <;> decide
  apply FOL.Context.deduction
  let Γ := [selector ψ, B, A]
  have hsel : FOL.Context Peano.Axiom Γ (selector ψ) := .head _ _
  have hor : FOL.Context Peano.Axiom Γ (M ⊔ E) := FOL.Context.conjunctionLeft hsel
  have ha : FOL.Context Peano.Axiom Γ A := .hypothesis (by simp [Γ])
  have hb : FOL.Context Peano.Axiom Γ B := .hypothesis (by simp [Γ])
  have hleft : FOL.Context Peano.Axiom Γ (M.imp L) := by
    apply FOL.Context.deduction
    have hm : FOL.Context Peano.Axiom (M :: Γ) M := .head _ _
    have hi : FOL.Context Peano.Axiom (M :: Γ) (less (.var 1) (.var 4)) :=
      .mp (.closed (PeanoBitFiniteSupport.bit_position (.var 4) (.var 1))) hm
    exact .mp (.mp (.closed (PeanoOrderTransitive.less_transitive_all
      (.var 1) (.var 4) (.var 0))) hi) (.under ha M)
  have hright : FOL.Context Peano.Axiom Γ (E.imp L) := by
    apply FOL.Context.deduction
    have he : FOL.Context Peano.Axiom (E :: Γ) E := .head _ _
    exact .mp (.mp (.closed (PeanoQuotientGap.less_left_congr
      (.var 5) (.var 1) (.var 0))) (FOL.Context.eqSymm he)) (.under hb E)
  exact or_elim hor hleft hright

end PASoundness.PeanoAX8SelectorBound

#print axioms PASoundness.PeanoAX8SelectorBound.selector_bounded
