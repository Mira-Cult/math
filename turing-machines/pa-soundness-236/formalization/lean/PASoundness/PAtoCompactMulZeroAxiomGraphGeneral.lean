import PASoundness.PAtoCompactMulZeroAxiomGraphConditional
import PASoundness.PAtoCompactMulZeroAxiomFrameShared

/-! Construct the actual guarded PA multiplication-by-zero axiom for arbitrary
terms, conditional on a finite K proof of guarded child graph existence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMulZeroAxiomGraphGeneral

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactMulZeroAxiomGraphConditional
open PASoundness.PAtoCompactMulZeroAxiomFrameShared PASoundness.PAtoCompactTermZeroGuarded
open PASoundness.PAtoCompactAddUnaryTotalityInduction

/-- Guarded PA `t * 0 = 0` for arbitrary t, from an explicit child graph
existence proof. No functionality or soundness premise is used. -/
noncomputable def mul_zero (t : Peano.Term)
    (child : let A := (Peano.mul t Peano.zero).equal Peano.zero
      let b := guardBase A + 2
      KDerivation (imp (guardFormula A).encode (existsCode b (termGraph id t b (b+64)).encode))) :
    KDerivation (guardedCode ((Peano.mul t Peano.zero).equal Peano.zero)) := by
  let product := Peano.mul t Peano.zero
  let A := product.equal Peano.zero
  let b := guardBase A
  have hscope : b = scopeBase A Fin.elim0 := by simp [b, guardBase, scopeBase]
  have hcover : ∀ a ∈ t.varFinset, id a ∈ A.freeVarFinset := by
    intro a ha
    simpa [A, product, Peano.mul, Peano.zero, eq_free, Term.varFinset] using ha
  have hnames : ∀ a ∈ product.varFinset, a < b := by
    intro a ha
    have hfree : a ∈ A.freeVarFinset := by
      simp only [A, eq_free, Finset.mem_union]
      exact Or.inl ha
    have hh := free_lt_scopeBase A Fin.elim0 a hfree
    omega
  have htotal := mul_zero_total_with_zero id A hcover child
  have hframe := shared_zero_to_frame product b hnames
  have h := PASoundness.CompactDerivations.compose htotal hframe
  unfold guardedCode code
  rw [original_shape]
  change KDerivation (imp (guardFormula A).encode
    (equalityFrame id product Peano.zero (scopeBase A Fin.elim0)).encode)
  rw [← hscope]
  simpa [A, product, Peano.mul, Peano.zero, binaryTerm, b] using h

theorem mul_zero_certificate (t : Peano.Term)
    (child : let A := (Peano.mul t Peano.zero).equal Peano.zero
      let b := guardBase A + 2
      KDerivation (imp (guardFormula A).encode (existsCode b (termGraph id t b (b+64)).encode))) :
    theoremCode (certificate (mul_zero t child)) =
      guardedCode ((Peano.mul t Peano.zero).equal Peano.zero) := certificate_correct _

end PASoundness.PAtoCompactMulZeroAxiomGraphGeneral

#print axioms PASoundness.PAtoCompactMulZeroAxiomGraphGeneral.mul_zero
#print axioms PASoundness.PAtoCompactMulZeroAxiomGraphGeneral.mul_zero_certificate
