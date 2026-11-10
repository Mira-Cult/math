import PASoundness.PAtoCompactPAAddZeroFrameTransport
import PASoundness.PAtoCompactPAAddZeroFrameBridge

/-! Compose one child value and a pointwise addition-zero graph constructor
into the actual guarded PA axiom. Both finite K inputs remain explicit. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPAAddZeroAxiomConditional
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactAddUnaryTotalityInduction
open PASoundness.PAtoCompactPAAddZeroFrameTransport PASoundness.PAtoCompactPAAddZeroFrameBridge

/-- Retain the second graph while transforming the first. -/
def shared_pair_of_child (t : Peano.Term) (b : Nat)
    (step : KDerivation (imp (termGraph id t b (b+2+64)).encode
      (termGraph id (Peano.add t Peano.zero) b (b+2)).encode)) :
    KDerivation (imp
      (andF (termGraph id t b (b+2+64))
        (termGraph id t b (b+2+termCost (Peano.add t Peano.zero)))).encode
      (andF (termGraph id (Peano.add t Peano.zero) b (b+2))
        (termGraph id t b (b+2+termCost (Peano.add t Peano.zero)))).encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let A := termGraph id t b (b+2+64)
  let B := termGraph id t b (b+2+termCost (Peano.add t Peano.zero))
  let C := termGraph id (Peano.add t Peano.zero) b (b+2)
  let Γ := [(andF A B).encode]
  have h : Context Γ (both A.encode B.encode) := by
    simpa [Γ, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using
      (Context.head [] (andF A B).encode)
  have hc : Context Γ C.encode := .mp (Context.conjunctionLeft h) (.closed step)
  have hb : Context Γ B.encode := Context.conjunctionRight h
  simpa [Γ, A, B, C, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using
    Context.conjunctionIntro hc hb

/-- The actual guarded PA `t+0=t` follows from guarded child graph existence
and a K construction of `t+0` at the same value. -/
noncomputable def add_zero_of_child_and_step (t : Peano.Term)
    (child : let a := Peano.add t Peano.zero
      let A := a.equal t
      let b := guardBase A
      KDerivation (imp (guardFormula A).encode
        (existsCode b (termGraph id t b (b+2)).encode)))
    (step : let a := Peano.add t Peano.zero
      let A := a.equal t
      let b := guardBase A
      KDerivation (imp (termGraph id t b (b+2+64)).encode
        (termGraph id a b (b+2)).encode)) :
    KDerivation (guardedCode ((Peano.add t Peano.zero).equal t)) := by
  let A := (Peano.add t Peano.zero).equal t
  let b := guardBase A
  have h := child_at_frame_bases_of_total t child
  have hp := existsCongr b (shared_pair_of_child t b step)
  exact add_zero_of_shared t (compose h hp)

/-- If the child lies in the addition-unary fragment, its guarded existence
is constructed internally; the pointwise K graph step remains explicit. -/
noncomputable def add_zero_addUnary_of_step (t : Peano.Term) (ht : AddUnaryTerm t)
    (step : let a := Peano.add t Peano.zero
      let A := a.equal t
      let b := guardBase A
      KDerivation (imp (termGraph id t b (b+2+64)).encode
        (termGraph id a b (b+2)).encode)) :
    KDerivation (guardedCode ((Peano.add t Peano.zero).equal t)) := by
  let A := (Peano.add t Peano.zero).equal t
  let b := guardBase A
  have h := guarded_child_at_frame_bases t ht
  have hp := existsCongr b (shared_pair_of_child t b step)
  exact add_zero_of_shared t (compose h hp)

theorem add_zero_of_child_and_step_certificate (t : Peano.Term)
    (child : let a := Peano.add t Peano.zero
      let A := a.equal t
      let b := guardBase A
      KDerivation (imp (guardFormula A).encode
        (existsCode b (termGraph id t b (b+2)).encode)))
    (step : let a := Peano.add t Peano.zero
      let A := a.equal t
      let b := guardBase A
      KDerivation (imp (termGraph id t b (b+2+64)).encode
        (termGraph id a b (b+2)).encode)) :
    theoremCode (certificate (add_zero_of_child_and_step t child step)) =
      guardedCode ((Peano.add t Peano.zero).equal t) := certificate_correct _

theorem add_zero_addUnary_of_step_certificate (t : Peano.Term) (ht : AddUnaryTerm t)
    (step : let a := Peano.add t Peano.zero
      let A := a.equal t
      let b := guardBase A
      KDerivation (imp (termGraph id t b (b+2+64)).encode
        (termGraph id a b (b+2)).encode)) :
    theoremCode (certificate (add_zero_addUnary_of_step t ht step)) =
      guardedCode ((Peano.add t Peano.zero).equal t) := certificate_correct _

#print axioms add_zero_of_child_and_step
#print axioms add_zero_addUnary_of_step
end PASoundness.PAtoCompactPAAddZeroAxiomConditional
