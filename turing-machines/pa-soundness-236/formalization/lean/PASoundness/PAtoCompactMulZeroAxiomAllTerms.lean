import PASoundness.PAtoCompactMulZeroAxiomGraphGeneral
import PASoundness.PAtoCompactAllTermsTotalityClosed

/-! Construct the literal guarded PA multiplication-by-zero axiom for every
PA term, using finite K term-graph totality. This does not prove any other PA
axiom family, proof transport, or PA soundness. -/
namespace PASoundness.PAtoCompactMulZeroAxiomAllTerms
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactVacuousEqualityAlignment
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] PASoundness.CompactProof.imp Cantor.pair Cantor.triangle

/-- Every PA term, including arbitrarily nested multiplication terms, has
its literal guarded `t * 0 = 0` PA axiom constructed as a finite K proof. -/
noncomputable def mul_zero (t : Peano.Term) :
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
  have child := PAtoCompactAllTermsTotalityClosed.guarded_total id A t (b+64) b
    (by omega) hnames hcover
  exact PAtoCompactMulZeroAxiomGraphGeneral.mul_zero t child

theorem mul_zero_certificate (t : Peano.Term) :
    theoremCode (certificate (mul_zero t)) =
      guardedCode ((Peano.mul t Peano.zero).equal Peano.zero) := certificate_correct _
end PASoundness.PAtoCompactMulZeroAxiomAllTerms
#print axioms PASoundness.PAtoCompactMulZeroAxiomAllTerms.mul_zero
#print axioms PASoundness.PAtoCompactMulZeroAxiomAllTerms.mul_zero_certificate
