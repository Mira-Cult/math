import PASoundness.PAtoCompactSuccCongruenceData

/-! Generic K generalization of a supplied pointwise proof to the exact
successor-order clause. All context-vacuity proofs remain explicit premises;
this module does not discharge the pointwise cases or prove congruence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccOrderPointLift
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactSuccCongruenceData

/-- The body after all four displayed universal order binders. -/
def pointMatrix : Formula := match newOrder with
  | .all _ (.all _ (.all _ (.all _ f))) => f
  | _ => .truth

/-- The exact substituted target has the original four binder labels. -/
theorem new_order_shape : newOrder = .all 2 (.all 4 (.all 3 (.all 5 pointMatrix))) := by decide

/-- A pointwise K proof in a context generalizes to the literal `newOrder`
when each context hypothesis comes with a proof of vacuity at each binder. -/
def context_point_lift (Γ : List Nat)
    (hv5 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 5 h)))
    (hv3 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 3 h)))
    (hv4 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 4 h)))
    (hv2 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 2 h)))
    (point : Context Γ pointMatrix.encode) : Context Γ newOrder.encode := by
  have h5 := Context.generalize 5 hv5 point
  have h3 := Context.generalize 3 hv3 h5
  have h4 := Context.generalize 4 hv4 h3
  have h2 := Context.generalize 2 hv2 h4
  rw [new_order_shape]
  exact h2

/-- Single-hypothesis version packaged as finite K proof data. -/
def point_lift (H : Nat)
    (hv5 : KDerivation (imp H (allCode 5 H)))
    (hv3 : KDerivation (imp H (allCode 3 H)))
    (hv4 : KDerivation (imp H (allCode 4 H)))
    (hv2 : KDerivation (imp H (allCode 2 H)))
    (point : KDerivation (imp H pointMatrix.encode)) :
    KDerivation (imp H newOrder.encode) := by
  have hp : Context [H] pointMatrix.encode := .mp (Context.head [] H) (.closed point)
  have h5 : ∀ h, h ∈ [H] → KDerivation (imp h (allCode 5 h)) := by
    intro h hh
    have he : h = H := by simpa using hh
    cases he
    exact hv5
  have h3 : ∀ h, h ∈ [H] → KDerivation (imp h (allCode 3 h)) := by
    intro h hh
    have he : h = H := by simpa using hh
    cases he
    exact hv3
  have h4 : ∀ h, h ∈ [H] → KDerivation (imp h (allCode 4 h)) := by
    intro h hh
    have he : h = H := by simpa using hh
    cases he
    exact hv4
  have h2 : ∀ h, h ∈ [H] → KDerivation (imp h (allCode 2 h)) := by
    intro h hh
    have he : h = H := by simpa using hh
    cases he
    exact hv2
  exact Context.closeEmpty (Context.deduction (context_point_lift [H] h5 h3 h4 h2 hp))

theorem point_lift_certificate (H : Nat)
    (hv5 : KDerivation (imp H (allCode 5 H)))
    (hv3 : KDerivation (imp H (allCode 3 H)))
    (hv4 : KDerivation (imp H (allCode 4 H)))
    (hv2 : KDerivation (imp H (allCode 2 H)))
    (point : KDerivation (imp H pointMatrix.encode)) :
    theoremCode (certificate (point_lift H hv5 hv3 hv4 hv2 point)) = imp H newOrder.encode :=
  certificate_correct (point_lift H hv5 hv3 hv4 hv2 point)

end PASoundness.PAtoCompactSuccOrderPointLift

#print axioms PASoundness.PAtoCompactSuccOrderPointLift.new_order_shape
#print axioms PASoundness.PAtoCompactSuccOrderPointLift.context_point_lift
#print axioms PASoundness.PAtoCompactSuccOrderPointLift.point_lift
#print axioms PASoundness.PAtoCompactSuccOrderPointLift.point_lift_certificate
