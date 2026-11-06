import Shared.ComplexityBridge.TM2Constant
import Shared.ComplexityBridge.TM2CutoffCompose
import Shared.Codes.UnaryWitnessVerifier

namespace Shared.ComplexityBridge.TM2UnaryLengthCheck

/-- The same executable length test used by the unary witness verifier. The
first list supplies the bound; the second is the candidate witness. -/
def fits (a : List Bool × List Bool) : Bool :=
  (Shared.Codes.UnaryWitnessVerifier.within a.2 a.1).1

theorem fits_correct (a : List Bool × List Bool) :
    fits a = true ↔ a.2.length ≤ a.1.length :=
  Shared.Codes.UnaryWitnessVerifier.within_correct a.2 a.1

/-- This is a canonical encoded-input TM2 theorem, not just a bound on Lean
list operations. The generic cutoff machine constructs the linear bound and
cleans its stacks; the constant checker supplies the success bit. -/
theorem fits_isPolyTime : ComplexityTheory.IsPolyTime fits := by
  have h := Shared.ComplexityBridge.TM2CutoffCompose.cutoffMask_isPolyTime
    [(1,1)] (fun _ => true)
    (Shared.ComplexityBridge.TM2Constant.isPolyTime (α := List Bool × List Bool) true)
  have heq : Shared.ComplexityBridge.TM2PairTotalPoly.cutoffMask [(1,1)] (fun _ => true) = fits := by
    funext a
    apply Bool.eq_iff_iff.mpr
    simp [Shared.ComplexityBridge.TM2PairTotalPoly.cutoffMask,
      Shared.Codes.NumericPolynomial.eval, fits_correct]
  rw [heq] at h
  exact h

end Shared.ComplexityBridge.TM2UnaryLengthCheck
