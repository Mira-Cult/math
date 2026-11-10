import PASoundness.PAtoCompactSuccInjectivityFrameCompose
import PASoundness.PAtoCompactVacuousQuantifierFree

/-! A finite K guarded PA successor-injectivity axiom follows from a supplied
pointwise equality-matrix proof. The construction transports the actual
allocated equality frames and eliminates the source value witnesses. The
pointwise K derivation is an explicit input, not quotient cancellation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccInjectivityGuardedFrame

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactVacuousQuantifierFree
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactSuccInjectivityFrameCompose

/-- The source PA successor-injectivity axiom. -/
def succInjective (t u : Peano.Term) : Peano.Formula :=
  ((Peano.succ t).equal (Peano.succ u)).imp (t.equal u)

/-- Given a pointwise finite K cancellation proof at a common allocation base,
construct the actual guarded PA axiom. Both term variables and guard free
names must lie below the selected base. No global graph totality, quotient
cancellation, or semantic soundness is assumed. -/
noncomputable def guarded_of_matrix (t u : Peano.Term) (base : Nat)
    (ht : ∀ a ∈ t.varFinset, a < base) (hu : ∀ a ∈ u.varFinset, a < base)
    (hguard : ∀ a ∈ (guardFormula (succInjective t u)).free, a < base)
    (pointwise : KDerivation (imp (guardFormula (succInjective t u)).encode
      (imp (matrix id (Peano.succ t) (Peano.succ u) base (base+1) (base+2)
        (base+2+termCost (Peano.succ t))
        (base+2+termCost (Peano.succ t)+termCost (Peano.succ u))).encode
        (equalityFrame id t u base).encode))) :
    KDerivation (guardedCode (succInjective t u)) := by
  let S : Peano.Formula := (Peano.succ t).equal (Peano.succ u)
  let T : Peano.Formula := t.equal u
  let sb := scopeBase S Fin.elim0
  let tb := scopeBase T Fin.elim0
  let H := guardFormula (succInjective t u)
  have hst : ∀ a ∈ (Peano.succ t).varFinset, a < sb := by
    intro a ha
    apply free_lt_scopeBase S Fin.elim0
    simp [S, eq_free, ha]
  have hsu : ∀ a ∈ (Peano.succ u).varFinset, a < sb := by
    intro a ha
    apply free_lt_scopeBase S Fin.elim0
    simp [S, eq_free, ha]
  have htt : ∀ a ∈ t.varFinset, a < tb := by
    intro a ha
    apply free_lt_scopeBase T Fin.elim0
    simp [T, eq_free, ha]
  have htu : ∀ a ∈ u.varFinset, a < tb := by
    intro a ha
    apply free_lt_scopeBase T Fin.elim0
    simp [T, eq_free, ha]
  have hstb : ∀ a ∈ (Peano.succ t).varFinset, a < base := by
    intro a ha
    apply ht a
    simpa [Peano.succ, Term.varFinset] using ha
  have hsub : ∀ a ∈ (Peano.succ u).varFinset, a < base := by
    intro a ha
    apply hu a
    simpa [Peano.succ, Term.varFinset] using ha
  have hs := (equalityFrame_base_transport id (Peano.succ t) (Peano.succ u) sb base
    (by intro a ha; simpa using hst a ha) (by intro a ha; simpa using hsu a ha)
    (by intro a ha; simpa using hstb a ha) (by intro a ha; simpa using hsub a ha)).1
  have hd := (equalityFrame_base_transport id t u base tb
    (by intro a ha; simpa using ht a ha) (by intro a ha; simpa using hu a ha)
    (by intro a ha; simpa using htt a ha) (by intro a ha; simpa using htu a ha)).1
  have hf := frame_of_matrix H (Peano.succ t) (Peano.succ u) t u base hguard pointwise
  change KDerivation (imp H.encode (imp (code S) (code T)))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [code S,H.encode]
  have hS : Context Γ (code S) := Context.head _ _
  have hH : Context Γ H.encode := .hypothesis (by simp [Γ])
  have hsrc : Context Γ (equalityFrame id (Peano.succ t) (Peano.succ u) base).encode := by
    apply Context.mp _ (.closed hs)
    simpa only [code, original_shape, S, sb] using hS
  have htarget := Context.mp hsrc (Context.mp hH (.closed hf))
  have hout := Context.mp htarget (.closed hd)
  simpa only [Γ, code, original_shape, T, tb] using hout

theorem guarded_of_matrix_certificate (t u : Peano.Term) (base : Nat)
    (ht : ∀ a ∈ t.varFinset, a < base) (hu : ∀ a ∈ u.varFinset, a < base)
    (hguard : ∀ a ∈ (guardFormula (succInjective t u)).free, a < base)
    (pointwise : KDerivation (imp (guardFormula (succInjective t u)).encode
      (imp (matrix id (Peano.succ t) (Peano.succ u) base (base+1) (base+2)
        (base+2+termCost (Peano.succ t))
        (base+2+termCost (Peano.succ t)+termCost (Peano.succ u))).encode
        (equalityFrame id t u base).encode))) :
    theoremCode (certificate (guarded_of_matrix t u base ht hu hguard pointwise)) =
      guardedCode (succInjective t u) := certificate_correct _

end PASoundness.PAtoCompactSuccInjectivityGuardedFrame

#print axioms PASoundness.PAtoCompactSuccInjectivityGuardedFrame.guarded_of_matrix
#print axioms PASoundness.PAtoCompactSuccInjectivityGuardedFrame.guarded_of_matrix_certificate
