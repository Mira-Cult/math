import PASoundness.PeanoBetaCRTRecordMerge

/-! PA elimination rules for the two disjoint cases of an appended row.
No sequence construction or trace-existence statement is asserted. -/
namespace PASoundness.PeanoBetaAppendCases
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

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

/-- Strict order and equality of the same two terms are incompatible in PA. -/
theorem less_excludes_equal (a b : Peano.Term) :
    FormulaProves ((less a b).imp (a.equal b).not) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let Γ := [a.equal b, less a b]
  have he : FOL.Context Peano.Axiom Γ (a.equal b) := FOL.Context.head _ _
  have hl : FOL.Context Peano.Axiom Γ (less a b) := .hypothesis (by simp [Γ])
  have hh : FOL.Context Peano.Axiom Γ (less b b) :=
    .mp (.mp (.closed (PeanoQuotientGap.less_left_congr a b b)) he) hl
  exact .mp (.closed (PeanoOrderIrreflexive.less_self b)) hh

/-- A guarded old row can be recovered from the old-or-appended relation. -/
theorem old_case (a b : Peano.Term) (old new : Peano.Formula) :
    FormulaProves ((((less a b ⊓ old) ⊔ ((a.equal b) ⊓ new))).imp
      ((less a b).imp old)) := by
  let L := less a b
  let E := a.equal b
  let D := (L ⊓ old) ⊔ (E ⊓ new)
  let Γ := [L, D]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hd : FOL.Context Peano.Axiom Γ D := .hypothesis (by simp [Γ])
  have hl : FOL.Context Peano.Axiom Γ L := FOL.Context.head _ _
  have hleft : FOL.Context Peano.Axiom Γ ((L ⊓ old).imp old) := by
    apply FOL.Context.deduction
    exact FOL.Context.conjunctionRight (FOL.Context.head _ _)
  have hright : FOL.Context Peano.Axiom Γ ((E ⊓ new).imp old) := by
    apply FOL.Context.deduction
    apply FOL.Context.dne
    apply FOL.Context.deduction
    have hpair : FOL.Context Peano.Axiom (old.not :: (E ⊓ new) :: Γ) (E ⊓ new) :=
      .hypothesis (by simp)
    have hbad : FOL.Context Peano.Axiom (old.not :: (E ⊓ new) :: Γ) E :=
      FOL.Context.conjunctionLeft hpair
    have hnot : FOL.Context Peano.Axiom (old.not :: (E ⊓ new) :: Γ) E.not :=
      .mp (.closed (less_excludes_equal a b)) (.under (.under hl _) _)
    exact .mp hnot hbad
  exact or_elim hd hleft hright

/-- At the appended index, the same relation yields the selected new row. -/
theorem new_case (a b : Peano.Term) (old new : Peano.Formula) :
    FormulaProves ((((less a b ⊓ old) ⊔ ((a.equal b) ⊓ new))).imp
      ((a.equal b).imp new)) := by
  let L := less a b
  let E := a.equal b
  let D := (L ⊓ old) ⊔ (E ⊓ new)
  let Γ := [E, D]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hd : FOL.Context Peano.Axiom Γ D := .hypothesis (by simp [Γ])
  have he : FOL.Context Peano.Axiom Γ E := FOL.Context.head _ _
  have hleft : FOL.Context Peano.Axiom Γ ((L ⊓ old).imp new) := by
    apply FOL.Context.deduction
    apply FOL.Context.dne
    apply FOL.Context.deduction
    have hpair : FOL.Context Peano.Axiom (new.not :: (L ⊓ old) :: Γ) (L ⊓ old) :=
      .hypothesis (by simp)
    have hl : FOL.Context Peano.Axiom (new.not :: (L ⊓ old) :: Γ) L :=
      FOL.Context.conjunctionLeft hpair
    have hnot : FOL.Context Peano.Axiom (new.not :: (L ⊓ old) :: Γ) E.not :=
      .mp (.closed (less_excludes_equal a b)) hl
    exact .mp hnot (.under (.under he _) _)
  have hright : FOL.Context Peano.Axiom Γ ((E ⊓ new).imp new) := by
    apply FOL.Context.deduction
    exact FOL.Context.conjunctionRight (FOL.Context.head _ _)
  exact or_elim hd hleft hright

end PASoundness.PeanoBetaAppendCases

#print axioms PASoundness.PeanoBetaAppendCases.less_excludes_equal
#print axioms PASoundness.PeanoBetaAppendCases.old_case
#print axioms PASoundness.PeanoBetaAppendCases.new_case
