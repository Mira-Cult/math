import PASoundness.PAtoCompactFirstFactorZeroGraph
import PASoundness.PAtoCompactMulZeroAxiomFrameShared
import PASoundness.PAtoCompactAllTermsTotalityClosed

/-! The guarded first-factor zero equation for arbitrary PA terms. The finite
K proof uses one shared output witness. It does not assume or prove the
second-factor successor law or general multiplication commutativity. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFirstFactorZeroAxiom

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactTermZeroGuarded
open PASoundness.PAtoCompactFirstFactorZeroGraph PASoundness.PAtoCompactMulZeroAxiomFrameShared

/-- For every PA term, construct the guarded K translation of `0 * t = 0`.
No K proof data or term-fragment hypothesis is supplied by the caller. -/
noncomputable def first_factor_zero (t : Peano.Term) :
    KDerivation (guardedCode ((Peano.mul Peano.zero t).equal Peano.zero)) := by
  let product := Peano.mul Peano.zero t
  let A := product.equal Peano.zero
  let b := guardBase A
  have hscope : b = scopeBase A Fin.elim0 := by simp [b, guardBase, scopeBase]
  have hcover : ∀ a ∈ t.varFinset, id a ∈ A.freeVarFinset := by
    intro a ha
    simpa [A, product, Peano.mul, Peano.zero, eq_free, Term.varFinset] using ha
  have hnames : ∀ a ∈ A.freeVarFinset, a < b+3 := by
    intro a ha
    have hh : a ≤ A.freeVarFinset.sup id := Finset.le_sup (f := id) ha
    dsimp [b, guardBase]
    omega
  have hprod : ∀ a ∈ product.varFinset, a < b := by
    intro a ha
    have hfree : a ∈ A.freeVarFinset := by
      simp only [A, eq_free, Finset.mem_union]
      exact Or.inl ha
    have hh := free_lt_scopeBase A Fin.elim0 a hfree
    omega
  have hchild := PAtoCompactAllTermsTotalityClosed.guarded_total id A t
    (b+2+64+termCost (.func .zero Fin.elim0 : Peano.Term)) (b+3)
    (by omega) hnames hcover
  have htotal := first_zero_total_with_zero id A hcover hchild
  have hframe := shared_zero_to_frame product b hprod
  have h := PASoundness.CompactDerivations.compose htotal hframe
  unfold guardedCode code
  rw [original_shape]
  change KDerivation (imp (guardFormula A).encode
    (equalityFrame id product Peano.zero (scopeBase A Fin.elim0)).encode)
  rw [← hscope]
  simpa [A, product, Peano.mul, Peano.zero, binaryTerm, b, Nat.add_assoc] using h

theorem first_factor_zero_certificate (t : Peano.Term) :
    theoremCode (certificate (first_factor_zero t)) =
      guardedCode ((Peano.mul Peano.zero t).equal Peano.zero) := certificate_correct _

end PASoundness.PAtoCompactFirstFactorZeroAxiom

#print axioms PASoundness.PAtoCompactFirstFactorZeroAxiom.first_factor_zero
#print axioms PASoundness.PAtoCompactFirstFactorZeroAxiom.first_factor_zero_certificate
