import PASoundness.PAtoCompactSuccInjectivityCanonicalFrame
import PASoundness.PAtoCompactSuccInjectMatrixToFrame
import PASoundness.PAtoCompactQuotSuccCancellationDynamicClosed

/-! Finite K proof of the genuine PA successor-injectivity axiom family. The
construction extracts child graphs from the translated antecedent; therefore
no global graph-totality premise is needed, even for compound PA terms. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccInjectivityProofClosed
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactHilbertBasis
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactSuccInjectivityGuardedFrame PASoundness.PAtoCompactSuccInjectivityCanonicalFrame
open PASoundness.PAtoCompactSuccInjectMatrixExtract PASoundness.PAtoCompactSuccInjectMatrixToFrame
open PASoundness.PAtoCompactQuotSuccCancellationDynamicClosed
attribute [local irreducible] PASoundness.CompactProof.imp PASoundness.Cantor.pair PASoundness.Cantor.triangle

/-- Every PA successor-injectivity axiom has an actual finite K proof under
its canonical free-variable guard. Both PA terms are arbitrary, including
addition and multiplication; no graph-totality proof is supplied. -/
noncomputable def guarded_successor_injective (t u : Peano.Term) :
    KDerivation (guardedCode (succInjective t u)) := by
  let g := guardBase (succInjective t u)
  let b := g+2
  let a := g
  let c := g+1
  let B := b+2+termCost (Peano.succ t)+termCost (Peano.succ u)+10
  have hb := canonical_bounds t u
  have ht : ∀ x ∈ t.varFinset, x < a := by
    intro x hx
    exact hb.1 x hx
  have hu : ∀ x ∈ u.varFinset, x < a := by
    intro x hx
    exact hb.2.1 x hx
  have hc : KDerivation (imp (succAt B a b).encode (imp (succAt B c (b+1)).encode
      (imp (equivAt B b (b+1)).encode (equivAt B a c).encode))) :=
    quotient_successor_cancellation B a c b (b+1)
      (by dsimp [B,b,a]; omega) (by dsimp [B,b,c]; omega)
      (by dsimp [B,b]; omega) (by dsimp [B,b]; omega)
  have hm := matrix_to_frame t u b a c (by dsimp [a,c]; omega) (by dsimp [b,c]; omega) ht hu hc
  let H := (guardFormula (succInjective t u)).encode
  have hp := KDerivation.mp hm (weakening _ H)
  apply guarded_of_matrix t u b
    (by intro x hx; have := ht x hx; dsimp [a,b]; omega)
    (by intro x hx; have := hu x hx; dsimp [a,b]; omega)
    (by intro x hx; have := hb.2.2 x hx; dsimp [b]; omega)
  simpa only [sourceMatrix, H] using hp

theorem guarded_successor_injective_certificate (t u : Peano.Term) :
    theoremCode (certificate (guarded_successor_injective t u)) =
      guardedCode (succInjective t u) := certificate_correct _

end PASoundness.PAtoCompactSuccInjectivityProofClosed
#print axioms PASoundness.PAtoCompactSuccInjectivityProofClosed.guarded_successor_injective
#print axioms PASoundness.PAtoCompactSuccInjectivityProofClosed.guarded_successor_injective_certificate
