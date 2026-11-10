import PASoundness.PeanoBitBelowPower

/-! Capture-safe arbitrary-term specialization of PA bit exclusion below a
literal power. This uses only the fixed-variable PA proof, not semantics. -/
namespace PASoundness.PeanoBitBelowPowerAll
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := rfl

private theorem subst_not (φ : Peano.Formula) (σ : Nat → Peano.Term) :
    φ.not.subst σ = (φ.subst σ).not := by
  simp [FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.mapTermRel]
  rfl

private def relation (a n p : Peano.Term) : Peano.Formula :=
  (pow2 n p).imp ((less a p).imp (bitFormula a n).not)

private theorem specialize (a n p : Peano.Term) (name : Nat) (t : Peano.Term)
    (h : FormulaProves (relation a n p)) : FormulaProves (relation
      (a.subst (fun y => if y = name then t else .var y))
      (n.subst (fun y => if y = name then t else .var y))
      (p.subst (fun y => if y = name then t else .var y))) := by
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (relation a n p) name t))
    (.generalize name h)
  simpa only [FOL.substAt, relation, subst_imp, subst_not, pow2_subst, less_subst,
    bitFormula_subst] using h₁

/-- If a code is below a literal power at index n, its nth bit is absent.
The terms may share variables: fresh names are introduced before instantiation. -/
theorem below_excludes_bit (a n p : Peano.Term) : FormulaProves
    ((pow2 n p).imp ((less a p).imp (bitFormula a n).not)) := by
  change FormulaProves (relation a n p)
  let support := a.varFinset ∪ n.varFinset ∪ p.varFinset
  let k := support.sup id + 6
  have hk : 6 ≤ k := by dsimp [k]; omega
  have fresh (j : Nat) (hj : k ≤ j) : j ∉ support := by
    intro h
    have hle : j ≤ support.sup id := Finset.le_sup (f := id) h
    dsimp [k] at hj
    omega
  have fa (j : Nat) (hj : k ≤ j) : j ∉ a.varFinset := by
    intro h; apply fresh j hj; simp [support, h]
  have fn (j : Nat) (hj : k ≤ j) : j ∉ n.varFinset := by
    intro h; apply fresh j hj; simp [support, h]
  have hbase : FormulaProves (relation (.var 0) (.var 1) (.var 5)) := by
    simpa [relation] using PeanoBitBelowPower.below_excludes_bit_vars
  have h1 := specialize _ _ _ 0 (.var k) hbase
  have h1' : FormulaProves (relation (.var k) (.var 1) (.var 5)) := by
    simpa [FirstOrder.Language.Term.subst] using h1
  have h2 := specialize _ _ _ 1 (.var (k+1)) h1'
  have h2' : FormulaProves (relation (.var k) (.var (k+1)) (.var 5)) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 1 by omega] using h2
  have h3 := specialize _ _ _ 5 (.var (k+2)) h2'
  have h3' : FormulaProves (relation (.var k) (.var (k+1)) (.var (k+2))) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 5 by omega,
      show k+1 ≠ 5 by omega] using h3
  have h4 := specialize _ _ _ k a h3'
  have h4' : FormulaProves (relation a (.var (k+1)) (.var (k+2))) := by
    simpa [FirstOrder.Language.Term.subst, show k+1 ≠ k by omega,
      show k+2 ≠ k by omega] using h4
  have h5 := specialize _ _ _ (k+1) n h4'
  have h5' : FormulaProves (relation a n (.var (k+2))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh a (k+1) n (fa _ (by omega)),
      show k+2 ≠ k+1 by omega] using h5
  have h6 := specialize _ _ _ (k+2) p h5'
  simpa [FirstOrder.Language.Term.subst,
    FOL.term_subst_fresh a (k+2) p (fa _ (by omega)),
    FOL.term_subst_fresh n (k+2) p (fn _ (by omega))] using h6

end PASoundness.PeanoBitBelowPowerAll

#print axioms PASoundness.PeanoBitBelowPowerAll.below_excludes_bit
