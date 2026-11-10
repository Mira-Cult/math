import PASoundness.PAtoCompactSeededSpanGlobalOrderPoint
import PASoundness.PAtoCompactFreeVacuity

/-! Lift the pointwise seeded-span comparison to all four point variables,
keeping the same named global guard fixed. The resulting order uses bound
labels 2,26,3,27; conversion to the canonical 2,4,3,5 order is separate. -/
namespace PASoundness.PAtoCompactSeededSpanGlobalOrderLift

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactSeededSpanGlobalOrderPoint

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def quantifiedOrder : Formula := .all 2 (.all 26 (.all 3 (.all 27 pointClause)))

/-- All four point variables are generalized under the same explicit named
global guard, with its free-vacuity checked separately at each variable. -/
def global_order_lift : KDerivation (imp globalGuard.encode quantifiedOrder.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [globalGuard.encode]
  have hg : Context Γ globalGuard.encode := .head _ _
  have hp : Context Γ pointClause.encode := .mp hg (.closed global_order_point)
  have hv (v : Nat) (fresh : v ∉ globalGuard.free) :
      ∀ h, h ∈ Γ → KDerivation (imp h (allCode v h)) := by
    intro h hh
    have he : h = globalGuard.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity v globalGuard fresh
  have hall := Context.generalize 2 (hv 2 (by decide))
    (Context.generalize 26 (hv 26 (by decide))
      (Context.generalize 3 (hv 3 (by decide))
        (Context.generalize 27 (hv 27 (by decide)) hp)))
  simpa only [quantifiedOrder,Formula.encode] using hall

theorem global_order_lift_certificate : theoremCode (certificate global_order_lift) =
    imp globalGuard.encode quantifiedOrder.encode := certificate_correct global_order_lift

end PASoundness.PAtoCompactSeededSpanGlobalOrderLift

#print axioms PASoundness.PAtoCompactSeededSpanGlobalOrderLift.quantifiedOrder
#print axioms PASoundness.PAtoCompactSeededSpanGlobalOrderLift.global_order_lift
#print axioms PASoundness.PAtoCompactSeededSpanGlobalOrderLift.global_order_lift_certificate
