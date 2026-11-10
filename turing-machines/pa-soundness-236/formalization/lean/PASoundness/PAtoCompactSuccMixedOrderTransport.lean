import PASoundness.PAtoCompactSuccOrderPointShape
import PASoundness.PAtoCompactSuccCongruenceMixedOrder
import PASoundness.PAtoCompactSuccMixedOrder45

/-! Capture-safe K transport of the three supplied mixed/top membership
comparisons to the exact successor-order comparison. This does not derive
coordinate equalities, graph edges, an isomorphism, or quotient congruence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccMixedOrderTransport
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactSuccOrderPointShape
open PASoundness.PAtoCompactSuccCongruenceMixedOrder PASoundness.PAtoCompactSuccMixedOrder45

/-- Named form of the literal comparison at endpoints (2,3),(4,5). -/
def cmp : Formula := namedBoth (.imp (.member 4 2) (.member 5 3))
  (.imp (.member 5 3) (.member 4 2))

def cmp4 : Formula := CompactNamed.replace 4 0 cmp
def cmp45 : Formula := CompactNamed.replace 5 1 cmp4
def cmp2 : Formula := CompactNamed.replace 2 0 cmp
def cmp23 : Formula := CompactNamed.replace 3 1 cmp2
def cmp234 : Formula := CompactNamed.replace 4 0 cmp23
def cmp2345 : Formula := CompactNamed.replace 5 1 cmp234

theorem cmp_code : cmp.encode = comparison := rfl
theorem cmp45_code : cmp45.encode = oldToTop := rfl
theorem cmp23_code : cmp23.encode = topToOld45 := rfl
theorem cmp2345_code : cmp2345.encode = topToTop := rfl

/-- The second edge is top: transport its two coordinates back from 0,1. -/
def old_top_transport : KDerivation (imp (both (equal 4 0) (equal 5 1))
    (imp oldToTop comparison)) := by
  have h4 := (CompactNamed.equalityReplace 4 0 cmp (by decide) (by decide)).2
  have h5 := (CompactNamed.equalityReplace 5 1 cmp4 (by decide) (by decide)).2
  change KDerivation (imp (equal 4 0) (imp cmp4.encode cmp.encode)) at h4
  change KDerivation (imp (equal 5 1) (imp cmp45.encode cmp4.encode)) at h5
  rw [cmp45_code] at h5
  rw [cmp_code] at h4
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldToTop,both (equal 4 0) (equal 5 1)]
  have he : Context Γ (both (equal 4 0) (equal 5 1)) := .hypothesis (by simp [Γ])
  have ho : Context Γ oldToTop := Context.head _ _
  have hm : Context Γ cmp4.encode := .mp ho (.mp (Context.conjunctionRight he) (.closed h5))
  exact .mp hm (.mp (Context.conjunctionLeft he) (.closed h4))

/-- The first edge is top: transport its coordinates back from 0,1. -/
def top_old_transport : KDerivation (imp (both (equal 2 0) (equal 3 1))
    (imp topToOld45 comparison)) := by
  have h2 := (CompactNamed.equalityReplace 2 0 cmp (by decide) (by decide)).2
  have h3 := (CompactNamed.equalityReplace 3 1 cmp2 (by decide) (by decide)).2
  change KDerivation (imp (equal 2 0) (imp cmp2.encode cmp.encode)) at h2
  change KDerivation (imp (equal 3 1) (imp cmp23.encode cmp2.encode)) at h3
  rw [cmp23_code] at h3
  rw [cmp_code] at h2
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [topToOld45,both (equal 2 0) (equal 3 1)]
  have he : Context Γ (both (equal 2 0) (equal 3 1)) := .hypothesis (by simp [Γ])
  have ho : Context Γ topToOld45 := Context.head _ _
  have hm : Context Γ cmp2.encode := .mp ho (.mp (Context.conjunctionRight he) (.closed h3))
  exact .mp hm (.mp (Context.conjunctionLeft he) (.closed h2))

/-- Both edges are top: transport all four coordinates. -/
def top_top_transport : KDerivation (imp (both (equal 2 0) (equal 3 1))
    (imp (both (equal 4 0) (equal 5 1)) (imp topToTop comparison))) := by
  have h2 := (CompactNamed.equalityReplace 2 0 cmp (by decide) (by decide)).2
  have h3 := (CompactNamed.equalityReplace 3 1 cmp2 (by decide) (by decide)).2
  have h4 := (CompactNamed.equalityReplace 4 0 cmp23 (by decide) (by decide)).2
  have h5 := (CompactNamed.equalityReplace 5 1 cmp234 (by decide) (by decide)).2
  change KDerivation (imp (equal 2 0) (imp cmp2.encode cmp.encode)) at h2
  change KDerivation (imp (equal 3 1) (imp cmp23.encode cmp2.encode)) at h3
  change KDerivation (imp (equal 4 0) (imp cmp234.encode cmp23.encode)) at h4
  change KDerivation (imp (equal 5 1) (imp cmp2345.encode cmp234.encode)) at h5
  rw [cmp2345_code] at h5
  rw [cmp_code] at h2
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [topToTop,both (equal 4 0) (equal 5 1),both (equal 2 0) (equal 3 1)]
  have he1 : Context Γ (both (equal 2 0) (equal 3 1)) := .hypothesis (by simp [Γ])
  have he2 : Context Γ (both (equal 4 0) (equal 5 1)) := .hypothesis (by simp [Γ])
  have ho : Context Γ topToTop := Context.head _ _
  have h234 : Context Γ cmp234.encode := .mp ho (.mp (Context.conjunctionRight he2) (.closed h5))
  have h23 : Context Γ cmp23.encode := .mp h234 (.mp (Context.conjunctionLeft he2) (.closed h4))
  have h2' : Context Γ cmp2.encode := .mp h23 (.mp (Context.conjunctionRight he1) (.closed h3))
  exact .mp h2' (.mp (Context.conjunctionLeft he1) (.closed h2))

theorem old_top_transport_certificate : theoremCode (certificate old_top_transport) =
    imp (both (equal 4 0) (equal 5 1)) (imp oldToTop comparison) := certificate_correct old_top_transport

theorem top_old_transport_certificate : theoremCode (certificate top_old_transport) =
    imp (both (equal 2 0) (equal 3 1)) (imp topToOld45 comparison) := certificate_correct top_old_transport

theorem top_top_transport_certificate : theoremCode (certificate top_top_transport) =
    imp (both (equal 2 0) (equal 3 1))
      (imp (both (equal 4 0) (equal 5 1)) (imp topToTop comparison)) := certificate_correct top_top_transport

end PASoundness.PAtoCompactSuccMixedOrderTransport

#print axioms PASoundness.PAtoCompactSuccMixedOrderTransport.old_top_transport
#print axioms PASoundness.PAtoCompactSuccMixedOrderTransport.top_old_transport
#print axioms PASoundness.PAtoCompactSuccMixedOrderTransport.top_top_transport
#print axioms PASoundness.PAtoCompactSuccMixedOrderTransport.old_top_transport_certificate
#print axioms PASoundness.PAtoCompactSuccMixedOrderTransport.top_old_transport_certificate
#print axioms PASoundness.PAtoCompactSuccMixedOrderTransport.top_top_transport_certificate
