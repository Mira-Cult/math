import PASoundness.PeanoBitLowerPreservation

/-! Capture-safe arbitrary-term specialization of lower-bit preservation. -/
namespace PASoundness.PeanoBitLowerPreservationAll
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoBitLowerPreservation

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

private def lowerRelation (b c i r s : Peano.Term) : Peano.Formula :=
  (pow2 c i).imp ((pow2 b s).imp ((less c b).imp (((bitFormula r c).imp (bitFormula (add r s) c)) ⊓ ((bitFormula (add r s) c).imp (bitFormula r c)))))

private theorem specialize (b c i r s : Peano.Term) (name : Nat) (t : Peano.Term)
    (h : FormulaProves (lowerRelation b c i r s)) : FormulaProves (lowerRelation
      (b.subst (fun y => if y = name then t else .var y))
      (c.subst (fun y => if y = name then t else .var y))
      (i.subst (fun y => if y = name then t else .var y))
      (r.subst (fun y => if y = name then t else .var y))
      (s.subst (fun y => if y = name then t else .var y))) := by
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (lowerRelation b c i r s) name t))
    (.generalize name h)
  simpa only [FOL.substAt, lowerRelation, subst_imp, subst_and, pow2_subst, bitFormula_subst, less_subst, FOL.equality_subst, PeanoArithmetic.add_subst, PeanoMultiplication.mul_subst] using h₁

/-- PA preserves a bit in both directions below an added power, for arbitrary
terms, including terms with overlapping free variables. The two literal
power hypotheses and strict index inequality are retained. -/
theorem lower_bits_preserved_all (b c i r s : Peano.Term) :
    FormulaProves ((pow2 c i).imp ((pow2 b s).imp ((less c b).imp (((bitFormula r c).imp (bitFormula (add r s) c)) ⊓ ((bitFormula (add r s) c).imp (bitFormula r c)))))) := by
  change FormulaProves (lowerRelation b c i r s)
  let support := b.varFinset ∪ c.varFinset ∪ i.varFinset ∪ r.varFinset ∪ s.varFinset
  let k := support.sup id + 8
  have hk : 8 ≤ k := by dsimp [k]; omega
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
  have hbase : FormulaProves (lowerRelation (.var 0) (.var 1) (.var 2) (.var 5) (.var 6)) := by
    simpa [lowerRelation] using lower_bits_preserved
  have h1 := specialize _ _ _ _ _ 0 (.var k) hbase
  have h1' : FormulaProves (lowerRelation (.var k) (.var 1) (.var 2) (.var 5) (.var 6)) := by
    simpa [FirstOrder.Language.Term.subst] using h1
  have h2 := specialize _ _ _ _ _ 1 (.var (k+1)) h1'
  have h2' : FormulaProves (lowerRelation (.var k) (.var (k+1)) (.var 2) (.var 5) (.var 6)) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 1 by omega] using h2
  have h3 := specialize _ _ _ _ _ 2 (.var (k+2)) h2'
  have h3' : FormulaProves (lowerRelation (.var k) (.var (k+1)) (.var (k+2)) (.var 5) (.var 6)) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 2 by omega,
      show k+1 ≠ 2 by omega] using h3
  have h4 := specialize _ _ _ _ _ 5 (.var (k+3)) h3'
  have h4' : FormulaProves (lowerRelation (.var k) (.var (k+1)) (.var (k+2)) (.var (k+3)) (.var 6)) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 5 by omega,
      show k+1 ≠ 5 by omega, show k+2 ≠ 5 by omega] using h4
  have h5 := specialize _ _ _ _ _ 6 (.var (k+4)) h4'
  have h5' : FormulaProves (lowerRelation (.var k) (.var (k+1)) (.var (k+2)) (.var (k+3)) (.var (k+4))) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 6 by omega,
      show k+1 ≠ 6 by omega, show k+2 ≠ 6 by omega, show k+3 ≠ 6 by omega] using h5
  have h6 := specialize _ _ _ _ _ k b h5'
  have h6' : FormulaProves (lowerRelation b (.var (k+1)) (.var (k+2)) (.var (k+3)) (.var (k+4))) := by
    simpa [FirstOrder.Language.Term.subst, show k+1 ≠ k by omega,
      show k+2 ≠ k by omega, show k+3 ≠ k by omega, show k+4 ≠ k by omega] using h6
  have h7 := specialize _ _ _ _ _ (k+1) c h6'
  have h7' : FormulaProves (lowerRelation b c (.var (k+2)) (.var (k+3)) (.var (k+4))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh b (k+1) c (fb _ (by omega)),
      show k+2 ≠ k+1 by omega, show k+3 ≠ k+1 by omega, show k+4 ≠ k+1 by omega] using h7
  have h8 := specialize _ _ _ _ _ (k+2) i h7'
  have h8' : FormulaProves (lowerRelation b c i (.var (k+3)) (.var (k+4))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh b (k+2) i (fb _ (by omega)),
      FOL.term_subst_fresh c (k+2) i (fc _ (by omega)),
      show k+3 ≠ k+2 by omega, show k+4 ≠ k+2 by omega] using h8
  have h9 := specialize _ _ _ _ _ (k+3) r h8'
  have h9' : FormulaProves (lowerRelation b c i r (.var (k+4))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh b (k+3) r (fb _ (by omega)),
      FOL.term_subst_fresh c (k+3) r (fc _ (by omega)),
      FOL.term_subst_fresh i (k+3) r (fi _ (by omega)), show k+4 ≠ k+3 by omega] using h9
  have h10 := specialize _ _ _ _ _ (k+4) s h9'
  simpa [lowerRelation, FirstOrder.Language.Term.subst,
    FOL.term_subst_fresh b (k+4) s (fb _ (by omega)),
    FOL.term_subst_fresh c (k+4) s (fc _ (by omega)),
    FOL.term_subst_fresh i (k+4) s (fi _ (by omega)),
    FOL.term_subst_fresh r (k+4) s (fr _ (by omega))] using h10

end PASoundness.PeanoBitLowerPreservationAll

#print axioms PASoundness.PeanoBitLowerPreservationAll.lower_bits_preserved_all
