import PASoundness.PeanoBitWitnessIntro

/-! Capture-safe arbitrary-term specialization of bit witness introduction. -/
namespace PASoundness.PeanoBitWitnessIntroAll
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoBitWitnessIntro

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := by rfl

private theorem subst_not (φ : Peano.Formula) (σ : Nat → Peano.Term) :
    φ.not.subst σ = (φ.subst σ).not := by
  simp [FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.mapTermRel]
  rfl

private theorem subst_and (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ ⊓ ψ).subst σ = (φ.subst σ) ⊓ (ψ.subst σ) := by
  change (φ.imp ψ.not).not.subst σ = ((φ.subst σ).imp (ψ.subst σ).not).not
  rw [subst_not, subst_imp, subst_not]

private def witnessRelation (b c i r s : Peano.Term) : Peano.Formula :=
  (pow2 c i).imp (((b.equal (add (add (mul r (add i i)) i) s)) ⊓ less s i).imp (bitFormula b c))

private theorem specialize (b c i r s : Peano.Term) (name : Nat) (t : Peano.Term)
    (h : FormulaProves (witnessRelation b c i r s)) : FormulaProves (witnessRelation
      (b.subst (fun y => if y = name then t else .var y))
      (c.subst (fun y => if y = name then t else .var y))
      (i.subst (fun y => if y = name then t else .var y))
      (r.subst (fun y => if y = name then t else .var y))
      (s.subst (fun y => if y = name then t else .var y))) := by
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (witnessRelation b c i r s) name t))
    (.generalize name h)
  simpa only [FOL.substAt, witnessRelation, subst_imp, subst_and, pow2_subst, bitFormula_subst, less_subst, FOL.equality_subst, PeanoArithmetic.add_subst, PeanoMultiplication.mul_subst] using h₁

/-- PA derives the literal bit predicate from explicit power, quotient, and
remainder witnesses for arbitrary terms, including overlapping variables. -/
theorem bit_of_witnesses_all (b c i r s : Peano.Term) :
    FormulaProves ((pow2 c i).imp (((b.equal (add (add (mul r (add i i)) i) s)) ⊓ less s i).imp (bitFormula b c))) := by
  change FormulaProves (witnessRelation b c i r s)
  let support := b.varFinset ∪ c.varFinset ∪ i.varFinset ∪ r.varFinset ∪ s.varFinset
  let k := support.sup id + 6
  have hk : 6 ≤ k := by dsimp [k]; omega
  have fresh (n : Nat) (hn : k ≤ n) : n ∉ support := by
    intro h
    have hle : n ≤ support.sup id := Finset.le_sup (f := id) h
    dsimp [k] at hn
    omega
  have fb (n : Nat) (hn : k ≤ n) : n ∉ b.varFinset := by
    intro h; apply fresh n hn; simp [support, h]
  have fc (n : Nat) (hn : k ≤ n) : n ∉ c.varFinset := by
    intro h; apply fresh n hn; simp [support, h]
  have fi (n : Nat) (hn : k ≤ n) : n ∉ i.varFinset := by
    intro h; apply fresh n hn; simp [support, h]
  have fr (n : Nat) (hn : k ≤ n) : n ∉ r.varFinset := by
    intro h; apply fresh n hn; simp [support, h]
  have hbase : FormulaProves (witnessRelation (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)) := by
    simpa [witnessRelation, row] using bit_of_witnesses
  have h1 := specialize _ _ _ _ _ 0 (.var k) hbase
  have h1' : FormulaProves (witnessRelation (.var k) (.var 1) (.var 2) (.var 3) (.var 4)) := by
    simpa [FirstOrder.Language.Term.subst] using h1
  have h2 := specialize _ _ _ _ _ 1 (.var (k+1)) h1'
  have h2' : FormulaProves (witnessRelation (.var k) (.var (k+1)) (.var 2) (.var 3) (.var 4)) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 1 by omega] using h2
  have h3 := specialize _ _ _ _ _ 2 (.var (k+2)) h2'
  have h3' : FormulaProves (witnessRelation (.var k) (.var (k+1)) (.var (k+2)) (.var 3) (.var 4)) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 2 by omega,
      show k+1 ≠ 2 by omega] using h3
  have h4 := specialize _ _ _ _ _ 3 (.var (k+3)) h3'
  have h4' : FormulaProves (witnessRelation (.var k) (.var (k+1)) (.var (k+2)) (.var (k+3)) (.var 4)) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 3 by omega,
      show k+1 ≠ 3 by omega, show k+2 ≠ 3 by omega] using h4
  have h5 := specialize _ _ _ _ _ 4 (.var (k+4)) h4'
  have h5' : FormulaProves (witnessRelation (.var k) (.var (k+1)) (.var (k+2)) (.var (k+3)) (.var (k+4))) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 4 by omega,
      show k+1 ≠ 4 by omega, show k+2 ≠ 4 by omega, show k+3 ≠ 4 by omega] using h5
  have h6 := specialize _ _ _ _ _ k b h5'
  have h6' : FormulaProves (witnessRelation b (.var (k+1)) (.var (k+2)) (.var (k+3)) (.var (k+4))) := by
    simpa [FirstOrder.Language.Term.subst, show k+1 ≠ k by omega,
      show k+2 ≠ k by omega, show k+3 ≠ k by omega, show k+4 ≠ k by omega] using h6
  have h7 := specialize _ _ _ _ _ (k+1) c h6'
  have h7' : FormulaProves (witnessRelation b c (.var (k+2)) (.var (k+3)) (.var (k+4))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh b (k+1) c (fb _ (by omega)),
      show k+2 ≠ k+1 by omega, show k+3 ≠ k+1 by omega, show k+4 ≠ k+1 by omega] using h7
  have h8 := specialize _ _ _ _ _ (k+2) i h7'
  have h8' : FormulaProves (witnessRelation b c i (.var (k+3)) (.var (k+4))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh b (k+2) i (fb _ (by omega)),
      FOL.term_subst_fresh c (k+2) i (fc _ (by omega)),
      show k+3 ≠ k+2 by omega, show k+4 ≠ k+2 by omega] using h8
  have h9 := specialize _ _ _ _ _ (k+3) r h8'
  have h9' : FormulaProves (witnessRelation b c i r (.var (k+4))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh b (k+3) r (fb _ (by omega)),
      FOL.term_subst_fresh c (k+3) r (fc _ (by omega)),
      FOL.term_subst_fresh i (k+3) r (fi _ (by omega)), show k+4 ≠ k+3 by omega] using h9
  have h10 := specialize _ _ _ _ _ (k+4) s h9'
  simpa [witnessRelation, FirstOrder.Language.Term.subst,
    FOL.term_subst_fresh b (k+4) s (fb _ (by omega)),
    FOL.term_subst_fresh c (k+4) s (fc _ (by omega)),
    FOL.term_subst_fresh i (k+4) s (fi _ (by omega)),
    FOL.term_subst_fresh r (k+4) s (fr _ (by omega))] using h10

end PASoundness.PeanoBitWitnessIntroAll

#print axioms PASoundness.PeanoBitWitnessIntroAll.bit_of_witnesses_all
