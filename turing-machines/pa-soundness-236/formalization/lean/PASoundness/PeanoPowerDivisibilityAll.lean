import PASoundness.PeanoPowerDivisibilityInduction

/-! Capture-safe term specialization for the PA power-divisibility relation. -/
namespace PASoundness.PeanoPowerDivisibilityAll
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoDivisibility

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := rfl

private theorem divides_subst (k d : Peano.Term) (σ : Nat → Peano.Term) :
    (divides k d).subst σ = divides (k.subst σ) (d.subst σ) := by
  unfold divides
  rw [SyntaxTransport.formula_subst_comp]
  congr 1
  funext y
  by_cases h0 : y = 0 <;> by_cases h1 : y = 1 <;> simp [h0, h1]

def relation (n i u p : Peano.Term) : Peano.Formula :=
  (pow2 i u).imp ((pow2 n p).imp
    ((less i n).imp (divides (add u u) p)))

private theorem specialize (n i u p : Peano.Term) (name : Nat) (t : Peano.Term)
    (h : FormulaProves (relation n i u p)) : FormulaProves (relation
      (n.subst (fun y => if y = name then t else .var y))
      (i.subst (fun y => if y = name then t else .var y))
      (u.subst (fun y => if y = name then t else .var y))
      (p.subst (fun y => if y = name then t else .var y))) := by
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (relation n i u p) name t))
    (.generalize name h)
  simpa only [FOL.substAt, relation, subst_imp, pow2_subst, less_subst,
    divides_subst, add_subst] using h₁

/-- The fixed-name PA derivation yields the same formula for arbitrary terms,
including terms with overlapping variables. The fixed-name derivation is an
explicit premise of this proof transformation. -/
theorem all_terms_of_fixed
    (hbase : FormulaProves (relation (.var 0) (.var 1) (.var 2) (.var 6)))
    (n i u p : Peano.Term) : FormulaProves (relation n i u p) := by
  let support := n.varFinset ∪ i.varFinset ∪ u.varFinset ∪ p.varFinset
  let k := support.sup id + 7
  have hk : 7 ≤ k := by dsimp [k]; omega
  have fresh (a : Nat) (ha : k ≤ a) : a ∉ support := by
    intro h
    have hle : a ≤ support.sup id := Finset.le_sup (f := id) h
    dsimp [k] at ha
    omega
  have fn (a : Nat) (ha : k ≤ a) : a ∉ n.varFinset := by
    intro h; apply fresh a ha; simp [support, h]
  have fi (a : Nat) (ha : k ≤ a) : a ∉ i.varFinset := by
    intro h; apply fresh a ha; simp [support, h]
  have fu (a : Nat) (ha : k ≤ a) : a ∉ u.varFinset := by
    intro h; apply fresh a ha; simp [support, h]
  have h1 := specialize _ _ _ _ 0 (.var k) hbase
  have h1' : FormulaProves (relation (.var k) (.var 1) (.var 2) (.var 6)) := by
    simpa [FirstOrder.Language.Term.subst] using h1
  have h2 := specialize _ _ _ _ 1 (.var (k+1)) h1'
  have h2' : FormulaProves (relation (.var k) (.var (k+1)) (.var 2) (.var 6)) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 1 by omega] using h2
  have h3 := specialize _ _ _ _ 2 (.var (k+2)) h2'
  have h3' : FormulaProves (relation (.var k) (.var (k+1)) (.var (k+2)) (.var 6)) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 2 by omega,
      show k+1 ≠ 2 by omega] using h3
  have h4 := specialize _ _ _ _ 6 (.var (k+3)) h3'
  have h4' : FormulaProves (relation (.var k) (.var (k+1)) (.var (k+2)) (.var (k+3))) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 6 by omega,
      show k+1 ≠ 6 by omega, show k+2 ≠ 6 by omega] using h4
  have h5 := specialize _ _ _ _ k n h4'
  have h5' : FormulaProves (relation n (.var (k+1)) (.var (k+2)) (.var (k+3))) := by
    simpa [FirstOrder.Language.Term.subst, show k+1 ≠ k by omega,
      show k+2 ≠ k by omega, show k+3 ≠ k by omega] using h5
  have h6 := specialize _ _ _ _ (k+1) i h5'
  have h6' : FormulaProves (relation n i (.var (k+2)) (.var (k+3))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh n (k+1) i (fn _ (by omega)),
      show k+2 ≠ k+1 by omega, show k+3 ≠ k+1 by omega] using h6
  have h7 := specialize _ _ _ _ (k+2) u h6'
  have h7' : FormulaProves (relation n i u (.var (k+3))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh n (k+2) u (fn _ (by omega)),
      FOL.term_subst_fresh i (k+2) u (fi _ (by omega)), show k+3 ≠ k+2 by omega] using h7
  have h8 := specialize _ _ _ _ (k+3) p h7'
  simpa [FirstOrder.Language.Term.subst,
    FOL.term_subst_fresh n (k+3) p (fn _ (by omega)),
    FOL.term_subst_fresh i (k+3) p (fi _ (by omega)),
    FOL.term_subst_fresh u (k+3) p (fu _ (by omega))] using h8

end PASoundness.PeanoPowerDivisibilityAll

#print axioms PASoundness.PeanoPowerDivisibilityAll.all_terms_of_fixed
