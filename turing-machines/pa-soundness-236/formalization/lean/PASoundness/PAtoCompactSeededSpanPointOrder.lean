import PASoundness.PAtoCompactSeededSpanPathOrder

/-! Pointwise seeded-span order assembled from the actual seed and path order
clauses, explicit seed endpoint membership, and conditional mixed guards.
No global order, bijection, graph existence, or addition congruence is claimed. -/
namespace PASoundness.PAtoCompactSeededSpanPointOrder

open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactSeededSpanBase
open PASoundness.PAtoCompactSeededSpanOrderCases PASoundness.PAtoCompactSeededSpanMixedOrder
open PASoundness.PAtoCompactSeededSpanOrderMixedAssembly PASoundness.PAtoCompactSeededSpanSeedOrder
open PASoundness.PAtoCompactSeededSpanPathOrder

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Each seed edge supplies membership only for its own two endpoints. -/
def seedEndpoints : Nat := both
  (imp firstSeed (both (member 40 2) (member 41 3)))
  (imp secondSeed (both (member 40 26) (member 41 27)))

/-- The seed/seed branch needs both seed memberships only when both actual
edges are seed edges; mixed branches do not require suffix points in the cut. -/
def seed_seed_from_guarded_endpoints : KDerivation
    (imp seedOrder.encode (imp seedEndpoints seedSeed)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [secondSeed,firstSeed,seedEndpoints,seedOrder.encode]
  have he2 : Context Γ secondSeed := .head _ _
  have he1 : Context Γ firstSeed := .hypothesis (by simp [Γ])
  have hend : Context Γ seedEndpoints := .hypothesis (by simp [Γ])
  have ho : Context Γ seedOrder.encode := .hypothesis (by simp [Γ])
  have hm1 : Context Γ (both (member 40 2) (member 41 3)) :=
    .mp he1 (Context.conjunctionLeft hend)
  have hm2 : Context Γ (both (member 40 26) (member 41 27)) :=
    .mp he2 (Context.conjunctionRight hend)
  have hd : Context Γ seedDomain := Context.conjunctionIntro (Context.conjunctionLeft hm1)
    (Context.conjunctionIntro (Context.conjunctionLeft hm2)
      (Context.conjunctionIntro (Context.conjunctionRight hm1) (Context.conjunctionRight hm2)))
  exact .mp he2 (.mp he1 (.mp hd (.mp ho (.closed seed_seed_from_order))))

theorem seed_seed_from_guarded_endpoints_certificate :
    theoremCode (certificate seed_seed_from_guarded_endpoints) =
      imp seedOrder.encode (imp seedEndpoints seedSeed) := certificate_correct seed_seed_from_guarded_endpoints

/-- Under the displayed seed order and membership, two source-to-image orders
and whole memberships, and conditional mixed cut guards at 40/41, two actual
seeded-span edges satisfy the pointwise order comparison. -/
def seeded_span_point_order : KDerivation (imp seededSpan.encode
    (imp (mixedPremises 40 41) (imp seedOrder.encode (imp seedEndpoints
      (imp orderGuard.encode (imp (graphFormula 9 2 3).encode
        (imp (graphFormula 9 26 27).encode comparison))))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let H1 := (graphFormula 9 2 3).encode
  let H2 := (graphFormula 9 26 27).encode
  let Γ := [H2,H1,orderGuard.encode,seedEndpoints,seedOrder.encode,mixedPremises 40 41,seededSpan.encode]
  have he2 : Context Γ H2 := .head _ _
  have he1 : Context Γ H1 := .hypothesis (by simp [Γ])
  have ho : Context Γ orderGuard.encode := .hypothesis (by simp [Γ])
  have hd : Context Γ seedEndpoints := .hypothesis (by simp [Γ])
  have hs : Context Γ seedOrder.encode := .hypothesis (by simp [Γ])
  have hm : Context Γ (mixedPremises 40 41) := .hypothesis (by simp [Γ])
  have hi : Context Γ seededSpan.encode := .hypothesis (by simp [Γ])
  have hseed : Context Γ seedSeed := .mp hd (.mp hs (.closed seed_seed_from_guarded_endpoints))
  have hpath : Context Γ pathPath := .mp ho (.closed path_path_from_orders)
  have hmwhole := Context.conjunctionRight (Context.conjunctionRight ho)
  have h02 : Context Γ (member 0 2) := Context.conjunctionLeft hmwhole
  have hmwhole := Context.conjunctionRight hmwhole
  have h026 : Context Γ (member 0 26) := Context.conjunctionLeft hmwhole
  have hmwhole := Context.conjunctionRight hmwhole
  have h83 : Context Γ (member 8 3) := Context.conjunctionLeft hmwhole
  have h827 : Context Γ (member 8 27) := Context.conjunctionRight hmwhole
  have hd1 : Context Γ (both (member 0 2) (member 8 3)) := Context.conjunctionIntro h02 h83
  have hd2 : Context Γ (both (member 0 26) (member 8 27)) := Context.conjunctionIntro h026 h827
  exact .mp he2 (.mp he1 (.mp hd2 (.mp hd1 (.mp hpath (.mp hseed
    (.mp hm (.mp hi (.closed (seeded_span_order_from_mixed 40 41)))))))))

theorem seeded_span_point_order_certificate : theoremCode (certificate seeded_span_point_order) =
    imp seededSpan.encode (imp (mixedPremises 40 41) (imp seedOrder.encode (imp seedEndpoints
      (imp orderGuard.encode (imp (graphFormula 9 2 3).encode
        (imp (graphFormula 9 26 27).encode comparison)))))) :=
  certificate_correct seeded_span_point_order

end PASoundness.PAtoCompactSeededSpanPointOrder

#print axioms PASoundness.PAtoCompactSeededSpanPointOrder.seedEndpoints
#print axioms PASoundness.PAtoCompactSeededSpanPointOrder.seed_seed_from_guarded_endpoints
#print axioms PASoundness.PAtoCompactSeededSpanPointOrder.seed_seed_from_guarded_endpoints_certificate
#print axioms PASoundness.PAtoCompactSeededSpanPointOrder.seeded_span_point_order
#print axioms PASoundness.PAtoCompactSeededSpanPointOrder.seeded_span_point_order_certificate
