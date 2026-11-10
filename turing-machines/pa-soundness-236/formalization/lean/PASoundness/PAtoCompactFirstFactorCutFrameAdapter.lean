import PASoundness.PAtoCompactFirstFactorCutContinuation
import PASoundness.PAtoCompactFirstFactorRawAllNames
import PASoundness.PAtoCompactFirstFactorFrameEncoding
import PASoundness.PAtoCompactRawSuccessorBinderBridge

/-! Construct the conditional cut-extension interface from the first-factor
shared-output frame and preserve the raw successor across its test-binder
conversion. These source-level constructions require kernel validation. -/
namespace PASoundness.PAtoCompactFirstFactorCutFrameAdapter

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactQuotientSuccessorTotality PASoundness.PAtoCompactSuccessorQuotientIntro
open PASoundness.PAtoCompactRawSuccessorBinderBridge
open PASoundness.PAtoCompactFirstFactorCutContinuation PASoundness.PAtoCompactFirstFactorRenameSyntax
open PASoundness.PAtoCompactFirstFactorRawAllNames PASoundness.PAtoCompactFirstFactorFrameEncoding
open PASoundness.PAtoCompactFirstFactorSuccessorTestRebind

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Construct the cut-extension proof at the allocated names. The raw
successor test is alpha-converted from the canonical e+10 binder to the fresh
binder chosen by `raw_frame`; it still describes the same input and output. -/
noncomputable def cut_extension (t u : Peano.Term) : CutExtension t u := by
  let A := (Peano.mul (Peano.succ t) u).equal (Peano.add (Peano.mul t u) u)
  let q := guardBase A
  let e := q+100
  let x := q+1
  let y := q+2
  let p := q+3
  let sx := q+4
  let w := freshTest x y p sx q
  let Dx := (domainAt e x).encode
  let Dy := (domainAt e y).encode
  let Dp := (domainAt e p).encode
  let R := (rawAt e x sx).encode
  let Ds := (domainAt e sx).encode
  let M := (mulAt e x y p).encode
  let Q := existsCode q (cutOutput e x y p sx q).encode
  have hw := freshTest_avoids_successor x y p sx q
  have hrename := raw_successor_rename x sx (e+10) w
    (by dsimp [e,x]; omega) (by dsimp [e,sx]; omega)
    (by simpa [w] using hw.1.symm) (by simpa [w] using hw.2.symm)
  have frame := raw_frame e x y p sx q
    (by dsimp [e,x]; omega) (by dsimp [e,y]; omega) (by dsimp [e,p]; omega)
    (by dsimp [e,sx]; omega) (by dsimp [e]; omega)
    (by dsimp [p]; omega) (by dsimp [y]; omega) (by dsimp [sx]; omega)
  have hframe : KDerivation (imp Dx (imp Dy (imp Dp (imp (successorCode x sx w) (imp M Q))))) := by
    have h := to_numeric e q w x y p sx frame
    simpa [guardedFrame, PAtoCompactFirstFactorOutputAlpha.body, cutOutput, Dx, Dy, Dp, M, Q] using h
  change KDerivation (imp Dx (imp Dy (imp Dp (imp R (imp Ds (imp M Q))))))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [M,Ds,R,Dp,Dy,Dx]
  have hm : Context Γ M := .head _ _
  have hr : Context Γ R := .hypothesis (by simp [Γ])
  have hp : Context Γ Dp := .hypothesis (by simp [Γ])
  have hy : Context Γ Dy := .hypothesis (by simp [Γ])
  have hx : Context Γ Dx := .hypothesis (by simp [Γ])
  have hr' : Context Γ (successorCode x sx (e+10)) := by
    simpa [R, rawAt, raw_successor_encode] using hr
  have hw' : Context Γ (successorCode x sx w) := .mp hr' (.closed hrename)
  exact .mp hm (.mp hw' (.mp hp (.mp hy (.mp hx (.closed hframe)))))

/-- The explicit continuation follows by assembling the independently
constructed shared-output frame with the candidate raw-successor interface. -/
noncomputable def first_factor_continuation (t u : Peano.Term) :
    PAtoCompactFirstFactorSuccessorReduction.RemainingContinuation t u :=
  continuation_from_cut t u (cut_extension t u)

/-- Construct finite K proof data for the guarded first-factor successor
formula. This source is not yet a kernel-validated theorem. -/
noncomputable def guarded_first_factor_successor (t u : Peano.Term) :
    KDerivation (guardedCode ((Peano.mul (Peano.succ t) u).equal (Peano.add (Peano.mul t u) u))) :=
  PAtoCompactFirstFactorSuccessorReduction.guarded_from_continuation t u
    (first_factor_continuation t u)

end PASoundness.PAtoCompactFirstFactorCutFrameAdapter

#print axioms PASoundness.PAtoCompactFirstFactorCutFrameAdapter.cut_extension
#print axioms PASoundness.PAtoCompactFirstFactorCutFrameAdapter.first_factor_continuation
#print axioms PASoundness.PAtoCompactFirstFactorCutFrameAdapter.guarded_first_factor_successor
