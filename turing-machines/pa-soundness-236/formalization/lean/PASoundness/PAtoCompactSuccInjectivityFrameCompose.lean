import PASoundness.PAtoCompactAllElimTermEquality
import PASoundness.PAtoCompactFreeVacuity

/-! Finite-K existential-frame elimination for an explicitly supplied
successor-injectivity matrix implication. The pointwise implication remains a
proof-data input; this module does not assert quotient cancellation, graph
totality, or a PA-axiom translation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccInjectivityFrameCompose

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactAllElimTermEquality

/-- Any finite K proof of a guarded equality-matrix implication to the target
frame lifts through both existential witnesses of the source frame. Witness
names are fresh for the guard's free names; no condition on target-term variable
names or values is assumed. -/
noncomputable def frame_of_matrix (H : Formula) (a b c d : Peano.Term) (base : Nat)
    (hH : ∀ x ∈ H.free, x < base)
    (pointwise : KDerivation (imp H.encode
      (imp (matrix id a b base (base+1) (base+2) (base+2+termCost a)
        (base+2+termCost a+termCost b)).encode
        (equalityFrame id c d base).encode))) :
    KDerivation (imp H.encode (imp (equalityFrame id a b base).encode
      (equalityFrame id c d base).encode)) := by
  let T := equalityFrame id c d base
  let M := matrix id a b base (base+1) (base+2) (base+2+termCost a)
    (base+2+termCost a+termCost b)
  have hf0 : base ∉ H.free := by intro h; have := hH base h; omega
  have hf1 : base+1 ∉ H.free := by intro h; have := hH (base+1) h; omega
  have tf0 : base ∉ T.free := by simp [T, equalityFrame, Formula.free]
  have tf1 : base+1 ∉ T.free := by simp [T, equalityFrame, Formula.free]
  have hp : KDerivation (imp H.encode (imp M.encode T.encode)) := pointwise
  have hlift := two_exists_left_guarded base (base+1) H.encode M.encode T.encode
    (free_vacuity base H hf0) (free_vacuity (base+1) H hf1)
    (free_vacuity base T tf0) (free_vacuity (base+1) T tf1) hp
  simpa [M, T, equalityFrame, matrix, Formula.encode] using hlift

theorem frame_of_matrix_certificate (H : Formula) (a b c d : Peano.Term) (base : Nat)
    (hH : ∀ x ∈ H.free, x < base)
    (pointwise : KDerivation (imp H.encode
      (imp (matrix id a b base (base+1) (base+2) (base+2+termCost a)
        (base+2+termCost a+termCost b)).encode
        (equalityFrame id c d base).encode))) :
    theoremCode (certificate (frame_of_matrix H a b c d base hH pointwise)) =
      imp H.encode (imp (equalityFrame id a b base).encode (equalityFrame id c d base).encode) :=
  certificate_correct _

end PASoundness.PAtoCompactSuccInjectivityFrameCompose

#print axioms PASoundness.PAtoCompactSuccInjectivityFrameCompose.frame_of_matrix
#print axioms PASoundness.PAtoCompactSuccInjectivityFrameCompose.frame_of_matrix_certificate
