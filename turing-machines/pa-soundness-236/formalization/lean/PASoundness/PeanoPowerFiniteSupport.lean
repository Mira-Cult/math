import PASoundness.PeanoPowerMonotonic
import PASoundness.PeanoPowerTotalityClosed
import PASoundness.PeanoBitBelowPowerAll
import PASoundness.PeanoInverseFutureAlignment

/-! PA finite support from a code strictly below a literal power. -/
namespace PASoundness.PeanoPowerFiniteSupport
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

/-- Failure of i<n implies n≤i in PA. -/
theorem not_less_implies_le (i n : Peano.Term) :
    FormulaProves ((less i n).not.imp (less n (succ i))) :=
  FOL.Derivation.compose
    (FOL.Derivation.contrapose (PeanoInverseFutureAlignment.not_less_succ_implies_gt n i))
    (.logical (.classical (less n (succ i))))

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

/-- PA transports a strict bound through a weak bound, for arbitrary terms. -/
theorem less_trans_le (a p q : Peano.Term) : FormulaProves
    ((less a p).imp ((less p (succ q)).imp (less a q))) := by
  let H := less a p
  let K := less p (succ q)
  let E := p.equal q
  let L := less p q
  let T := less a q
  let Γ := [K,H]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hh : FOL.Context Peano.Axiom Γ H := .hypothesis (by simp [Γ])
  have hk : FOL.Context Peano.Axiom Γ K := .head _ _
  have he : FOL.Context Peano.Axiom Γ (E.imp T) := by
    apply FOL.Context.deduction
    exact .mp (.mp (.closed (PeanoMultiplyQuotientStep.less_right_congr a p q))
      (.head _ _)) (.under hh E)
  have hl : FOL.Context Peano.Axiom Γ (L.imp T) := by
    apply FOL.Context.deduction
    exact .mp (.mp (.closed (PeanoOrderTransitive.less_transitive_all a p q))
      (.under hh L)) (.head _ _)
  have hc : FOL.Context Peano.Axiom Γ (E ⊔ L) :=
    .mp (.closed (PeanoCommonMultiple.BoundSplit.less_successor_cases p q)) hk
  exact or_elim hc he hl

private def rel (i n : Peano.Term) : Peano.Formula :=
  (pow2 i (.var 2)).imp ((pow2 n (.var 6)).imp
    ((less i (succ n)).imp (less (.var 2) (succ (.var 6)))))

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := rfl

private theorem specialize (i n : Peano.Term) (name : Nat) (t : Peano.Term)
    (hn2 : name ≠ 2) (hn6 : name ≠ 6)
    (h : FormulaProves (rel i n)) : FormulaProves (rel
      (i.subst (fun y => if y = name then t else .var y))
      (n.subst (fun y => if y = name then t else .var y))) := by
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (rel i n) name t))
    (.generalize name h)
  simpa [FOL.substAt, rel, subst_imp, pow2_subst, less_subst, succ_subst,
    FirstOrder.Language.Term.subst, show 2 ≠ name from Ne.symm hn2,
    show 6 ≠ name from Ne.symm hn6] using h₁

theorem swapped : FormulaProves (rel (.var 0) (.var 1)) := by
  have h0 : FormulaProves (rel (.var 1) (.var 0)) := PeanoPowerMonotonic.weak_power_monotonic
  have h1 := specialize (.var 1) (.var 0) 0 (.var 10) (by decide) (by decide) h0
  have h1' : FormulaProves (rel (.var 1) (.var 10)) := by
    simpa [FirstOrder.Language.Term.subst] using h1
  have h2 := specialize (.var 1) (.var 10) 1 (.var 0) (by decide) (by decide) h1'
  have h2' : FormulaProves (rel (.var 0) (.var 10)) := by
    simpa [FirstOrder.Language.Term.subst] using h2
  have h3 := specialize (.var 0) (.var 10) 10 (.var 1) (by decide) (by decide) h2'
  simpa [FirstOrder.Language.Term.subst] using h3


/-- PA constructs a literal power at the index named 1, with output 6. -/
theorem power_exists_at_index : FormulaProves
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

/-- Every bit at or above index n is absent when the code is below the
literal power at n. Names 0, 1, 2, and 3 are n, i, p, and the code. -/
theorem finite_support_vars : FormulaProves
    ((pow2 (.var 0) (.var 2)).imp ((less (.var 3) (.var 2)).imp
      ((less (.var 1) (.var 0)).not.imp (bitFormula (.var 3) (.var 1)).not))) := by
  let P := pow2 (.var 0) (.var 2)
  let A := less (.var 3) (.var 2)
  let N := (less (.var 1) (.var 0)).not
  let B := bitFormula (.var 3) (.var 1)
  let Q := pow2 (.var 1) (.var 6)
  let G := P.imp (A.imp (N.imp B.not))
  have hbody : FormulaProves (Q.imp G) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    let Γ := [N,A,P,Q]
    have hn : FOL.Context Peano.Axiom Γ N := .head _ _
    have ha : FOL.Context Peano.Axiom Γ A := .hypothesis (by simp [Γ])
    have hp : FOL.Context Peano.Axiom Γ P := .hypothesis (by simp [Γ])
    have hq : FOL.Context Peano.Axiom Γ Q := .hypothesis (by simp [Γ])
    have hni : FOL.Context Peano.Axiom Γ (less (.var 0) (succ (.var 1))) :=
      .mp (.closed (not_less_implies_le (.var 1) (.var 0))) hn
    have hpq : FOL.Context Peano.Axiom Γ (less (.var 2) (succ (.var 6))) :=
      .mp (.mp (.mp (.closed swapped) hp) hq) hni
    have haq : FOL.Context Peano.Axiom Γ (less (.var 3) (.var 6)) :=
      .mp (.mp (.closed (less_trans_le (.var 3) (.var 2) (.var 6))) ha) hpq
    exact .mp (.mp (.closed (PeanoBitBelowPowerAll.below_excludes_bit
      (.var 3) (.var 1) (.var 6))) hq) haq
  have hfresh : 6 ∉ G.freeVarFinset := by decide
  exact .mp (PeanoBitPositionReduction.exists_elim 6 hfresh hbody) power_exists_at_index

end PASoundness.PeanoPowerFiniteSupport

#print axioms PASoundness.PeanoPowerFiniteSupport.finite_support_vars
