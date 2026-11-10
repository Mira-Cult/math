import PASoundness.PAtoCompactGuardedVacuousPure
import PASoundness.PAtoCompactGuardedModusPonensFull

/-! Guarded generalization for the bottom/implication fragment, using the
proved vacuous-axiom instances and unrestricted guarded modus ponens. This is
not generalization for arbitrary PA formulas. -/
namespace PASoundness.PAtoCompactGeneralizationPure

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactGuardedBridge

/-- Actual finite K proof transformer for a pure source formula. -/
def generalize (φ : Peano.Formula) (h : PAtoCompactGuardedVacuousPure.Pure φ)
    (x : Nat) (d : KDerivation (guardedCode φ)) :
    KDerivation (guardedCode (FOL.allAt x φ)) :=
  PAtoCompactGuardedModusPonensFull.modusPonens φ (FOL.allAt x φ)
    (PAtoCompactGuardedVacuousPure.vacuous φ h x) d

theorem generalize_certificate (φ : Peano.Formula) (h : PAtoCompactGuardedVacuousPure.Pure φ)
    (x : Nat) (d : KDerivation (guardedCode φ)) :
    theoremCode (certificate (generalize φ h x d)) = guardedCode (FOL.allAt x φ) :=
  certificate_correct _

end PASoundness.PAtoCompactGeneralizationPure

#print axioms PASoundness.PAtoCompactGeneralizationPure.generalize
#print axioms PASoundness.PAtoCompactGeneralizationPure.generalize_certificate
