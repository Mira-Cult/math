import PASoundness.PAtoCompactMulZeroAxiomGraphGeneral
import PASoundness.PAtoCompactAddUnaryTotalityClosed

/-! Discharge the guarded child-graph premise for the addition-unary term
fragment. This is a corollary of the arbitrary-term conditional PA axiom. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMulZeroAxiomGraphFragment

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactVacuousEqualityAlignment
open PASoundness.PAtoCompactAddUnaryTotalityInduction

/-- For t built from variables, zero, successor and addition, construct the
literal guarded PA `t * 0 = 0` axiom without supplied K proof data. -/
noncomputable def mul_zero (t : Peano.Term) (ht : AddUnaryTerm t) :
    KDerivation (guardedCode ((Peano.mul t Peano.zero).equal Peano.zero)) := by
  let A := (Peano.mul t Peano.zero).equal Peano.zero
  let b := guardBase A + 2
  have hnames : ∀ z ∈ A.freeVarFinset, z < b := by
    intro z hz
    have hh : z ≤ A.freeVarFinset.sup id := Finset.le_sup (f := id) hz
    dsimp [b, guardBase]
    omega
  have hcover : ∀ a ∈ t.varFinset, id a ∈ A.freeVarFinset := by
    intro a ha
    simpa [A, Peano.mul, Peano.zero, eq_free, Term.varFinset] using ha
  have child := PAtoCompactAddUnaryGuardedTotality.guarded_total id A ht
    PAtoCompactAddUnaryTotalityClosed.additionExistence (b+64) b
    (by omega) hnames hcover
  exact PAtoCompactMulZeroAxiomGraphGeneral.mul_zero t child

theorem mul_zero_certificate (t : Peano.Term) (ht : AddUnaryTerm t) :
    theoremCode (certificate (mul_zero t ht)) =
      guardedCode ((Peano.mul t Peano.zero).equal Peano.zero) := certificate_correct _

end PASoundness.PAtoCompactMulZeroAxiomGraphFragment

#print axioms PASoundness.PAtoCompactMulZeroAxiomGraphFragment.mul_zero
#print axioms PASoundness.PAtoCompactMulZeroAxiomGraphFragment.mul_zero_certificate
