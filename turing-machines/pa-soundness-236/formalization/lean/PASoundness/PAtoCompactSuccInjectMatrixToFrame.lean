import PASoundness.PAtoCompactSuccInjectFrameFree
import PASoundness.PAtoCompactSuccInjectiveChildMatrix
import PASoundness.PAtoCompactInjectivityWitnessElimination
import PASoundness.PAtoCompactFreeVacuity

/-! Eliminate both genuine successor child witnesses from the translated PA
successor-equality matrix. Quotient-successor cancellation remains an explicit
finite K derivation input. No term totality or soundness theorem is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccInjectMatrixToFrame
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactSuccInjectMatrixExtract PASoundness.PAtoCompactSuccInjectFrameFree
open PASoundness.PAtoCompactSuccInjectiveChildMatrix PASoundness.PAtoCompactInjectivityWitnessElimination
open PASoundness.PAtoCompactSuccTermSpareAlpha PASoundness.PAtoCompactFreeVacuity
attribute [local irreducible] PASoundness.CompactProof.imp PASoundness.Cantor.pair PASoundness.Cantor.triangle

/-- If both term supports lie below fresh witnesses a<c<b, the actual
successor-equality matrix entails the target equality frame, given a finite K
quotient-successor cancellation derivation. Source variables and represented
values may coincide; the inequalities concern syntactic labels only. -/
noncomputable def matrix_to_frame (t u : Peano.Term) (b a c : Nat)
    (hac : a < c) (hcb : c < b)
    (ht : ∀ x ∈ t.varFinset, x < a) (hu : ∀ x ∈ u.varFinset, x < a)
    (cancel : let B := b+2+termCost (Peano.succ t)+termCost (Peano.succ u)+10
      KDerivation (imp (succAt B a b).encode (imp (succAt B c (b+1)).encode
        (imp (equivAt B b (b+1)).encode (equivAt B a c).encode)))) :
    KDerivation (imp (sourceMatrix t u b).encode (equalityFrame id t u b).encode) := by
  let M := sourceMatrix t u b
  let T := spareBody id t b (b+2) a
  let U := spareBody id u (b+1) (b+2+termCost (Peano.succ t)) c
  let E := equivAt (b+2+termCost (Peano.succ t)+termCost (Peano.succ u)) b (b+1)
  let F := equalityFrame id t u b
  have hA := first_child t u b a (by omega) ht
  have hC := second_child t u b c hcb (by intro x hx; have := hu x hx; omega)
  have hE := output_equiv t u b
  have hlocal := children_to_frame t u b a c (by omega) hcb
    (by intro x hx; have := ht x hx; omega)
    (by intro x hx; have := hu x hx; omega) cancel
  have ha := source_target_free t u b a (by omega) ht hu
  have hc := source_target_free t u b c hcb
    (by intro x hx; have := ht x hx; omega)
    (by intro x hx; have := hu x hx; omega)
  have htc := second_spare_not_first_body t b a c hac hcb ht
  have h := eliminate_two_witnesses a c M.encode T.encode U.encode E.encode F.encode
    hA hC hE (by simpa only [spareBody, T, U, E, F] using hlocal)
    (free_vacuity a M ha.1) (free_vacuity c M hc.1)
    (free_vacuity c T htc) (free_vacuity a F ha.2) (free_vacuity c F hc.2)
  exact h

theorem matrix_to_frame_certificate (t u : Peano.Term) (b a c : Nat)
    (hac : a < c) (hcb : c < b)
    (ht : ∀ x ∈ t.varFinset, x < a) (hu : ∀ x ∈ u.varFinset, x < a)
    (cancel : let B := b+2+termCost (Peano.succ t)+termCost (Peano.succ u)+10
      KDerivation (imp (succAt B a b).encode (imp (succAt B c (b+1)).encode
        (imp (equivAt B b (b+1)).encode (equivAt B a c).encode)))) :
    theoremCode (certificate (matrix_to_frame t u b a c hac hcb ht hu cancel)) =
      imp (sourceMatrix t u b).encode (equalityFrame id t u b).encode := certificate_correct _

end PASoundness.PAtoCompactSuccInjectMatrixToFrame
#print axioms PASoundness.PAtoCompactSuccInjectMatrixToFrame.matrix_to_frame
#print axioms PASoundness.PAtoCompactSuccInjectMatrixToFrame.matrix_to_frame_certificate
