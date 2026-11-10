import PASoundness.PeanoPowerFiniteSupport

/-! Capture-safe specialization of the literal power finite-support theorem. -/
namespace PASoundness.PeanoPowerFiniteSupportAll
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := rfl

private theorem subst_not (φ : Peano.Formula) (σ : Nat → Peano.Term) :
    φ.not.subst σ = (φ.subst σ).not := by
  simp [FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.mapTermRel]
  rfl

private def relation (n i p a : Peano.Term) : Peano.Formula :=
  (pow2 n p).imp ((less a p).imp ((less i n).not.imp (bitFormula a i).not))

private theorem specialize (n i p a : Peano.Term) (name : Nat) (t : Peano.Term)
    (h : FormulaProves (relation n i p a)) : FormulaProves (relation
      (n.subst (fun y => if y = name then t else .var y))
      (i.subst (fun y => if y = name then t else .var y))
      (p.subst (fun y => if y = name then t else .var y))
      (a.subst (fun y => if y = name then t else .var y))) := by
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (relation n i p a) name t))
    (.generalize name h)
  simpa only [FOL.substAt, relation, subst_imp, subst_not, pow2_subst, less_subst,
    bitFormula_subst] using h₁

/-- PA proves that positions outside n have no bit when the code is below
the power at n. All four terms may share free variables. -/
theorem finite_support (n i p a : Peano.Term) : FormulaProves
    ((pow2 n p).imp ((less a p).imp ((less i n).not.imp (bitFormula a i).not))) := by
  change FormulaProves (relation n i p a)
  let support := n.varFinset ∪ i.varFinset ∪ p.varFinset ∪ a.varFinset
  let k := support.sup id + 4
  have hk : 4 ≤ k := by dsimp [k]; omega
  have fresh (x : Nat) (hx : k ≤ x) : x ∉ support := by
    intro h
    have hle : x ≤ support.sup id := Finset.le_sup (f := id) h
    dsimp [k] at hx
    omega
  have fn (x : Nat) (hx : k ≤ x) : x ∉ n.varFinset := by
    intro h; apply fresh x hx; simp [support, h]
  have fi (x : Nat) (hx : k ≤ x) : x ∉ i.varFinset := by
    intro h; apply fresh x hx; simp [support, h]
  have fp (x : Nat) (hx : k ≤ x) : x ∉ p.varFinset := by
    intro h; apply fresh x hx; simp [support, h]
  have h1 := specialize _ _ _ _ 0 (.var k) PeanoPowerFiniteSupport.finite_support_vars
  have h1' : FormulaProves (relation (.var k) (.var 1) (.var 2) (.var 3)) := by
    simpa [FirstOrder.Language.Term.subst] using h1
  have h2 := specialize _ _ _ _ 1 (.var (k+1)) h1'
  have h2' : FormulaProves (relation (.var k) (.var (k+1)) (.var 2) (.var 3)) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 1 by omega] using h2
  have h3 := specialize _ _ _ _ 2 (.var (k+2)) h2'
  have h3' : FormulaProves (relation (.var k) (.var (k+1)) (.var (k+2)) (.var 3)) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 2 by omega,
      show k+1 ≠ 2 by omega] using h3
  have h4 := specialize _ _ _ _ 3 (.var (k+3)) h3'
  have h4' : FormulaProves (relation (.var k) (.var (k+1)) (.var (k+2)) (.var (k+3))) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 3 by omega,
      show k+1 ≠ 3 by omega, show k+2 ≠ 3 by omega] using h4
  have h5 := specialize _ _ _ _ k n h4'
  have h5' : FormulaProves (relation n (.var (k+1)) (.var (k+2)) (.var (k+3))) := by
    simpa [FirstOrder.Language.Term.subst, show k+1 ≠ k by omega,
      show k+2 ≠ k by omega, show k+3 ≠ k by omega] using h5
  have h6 := specialize _ _ _ _ (k+1) i h5'
  have h6' : FormulaProves (relation n i (.var (k+2)) (.var (k+3))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh n (k+1) i (fn _ (by omega)),
      show k+2 ≠ k+1 by omega, show k+3 ≠ k+1 by omega] using h6
  have h7 := specialize _ _ _ _ (k+2) p h6'
  have h7' : FormulaProves (relation n i p (.var (k+3))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh n (k+2) p (fn _ (by omega)),
      FOL.term_subst_fresh i (k+2) p (fi _ (by omega)), show k+3 ≠ k+2 by omega] using h7
  have h8 := specialize _ _ _ _ (k+3) a h7'
  simpa [FirstOrder.Language.Term.subst,
    FOL.term_subst_fresh n (k+3) a (fn _ (by omega)),
    FOL.term_subst_fresh i (k+3) a (fi _ (by omega)),
    FOL.term_subst_fresh p (k+3) a (fp _ (by omega))] using h8

end PASoundness.PeanoPowerFiniteSupportAll

#print axioms PASoundness.PeanoPowerFiniteSupportAll.finite_support
