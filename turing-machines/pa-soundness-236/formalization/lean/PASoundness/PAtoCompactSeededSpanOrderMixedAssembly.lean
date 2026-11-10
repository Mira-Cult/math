import PASoundness.PAtoCompactSeededSpanMixedOrder

/-! Assemble the seeded-span point order using the proved mixed-case
construction, with the two same-kind cases and conditional mixed guards
remaining explicit object-level K antecedents. -/
namespace PASoundness.PAtoCompactSeededSpanOrderMixedAssembly

open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactSeededSpanBase
open PASoundness.PAtoCompactSeededSpanOrderCases PASoundness.PAtoCompactSeededSpanMixedOrder

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def seedSeed : Nat := imp firstSeed (imp secondSeed comparison)
def pathPath : Nat := imp firstPath (imp secondPath comparison)

/-- For the actual two graph-9 edges, order agreement follows from the seed
case, path case, and explicit mixed prefix/outside guards. -/
def seeded_span_order_from_mixed (sourceCut targetCut : Nat) : KDerivation
    (imp seededSpan.encode (imp (mixedPremises sourceCut targetCut)
      (imp seedSeed (imp pathPath (imp (both (member 0 2) (member 8 3))
        (imp (both (member 0 26) (member 8 27)) (imp (graphFormula 9 2 3).encode
          (imp (graphFormula 9 26 27).encode comparison)))))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let D1 := both (member 0 2) (member 8 3)
  let D2 := both (member 0 26) (member 8 27)
  let H1 := (graphFormula 9 2 3).encode
  let H2 := (graphFormula 9 26 27).encode
  let Γ := [H2,H1,D2,D1,pathPath,seedSeed,mixedPremises sourceCut targetCut,seededSpan.encode]
  have h2 : Context Γ H2 := .head _ _
  have h1 : Context Γ H1 := .hypothesis (by simp [Γ])
  have hd2 : Context Γ D2 := .hypothesis (by simp [Γ])
  have hd1 : Context Γ D1 := .hypothesis (by simp [Γ])
  have hpath : Context Γ pathPath := .hypothesis (by simp [Γ])
  have hseed : Context Γ seedSeed := .hypothesis (by simp [Γ])
  have hguards : Context Γ (mixedPremises sourceCut targetCut) := .hypothesis (by simp [Γ])
  have hspan : Context Γ seededSpan.encode := .hypothesis (by simp [Γ])
  have hmixed : Context Γ mixedConclusions :=
    .mp hguards (.closed (mixed_order_branches sourceCut targetCut))
  have hbranches : Context Γ branches := Context.conjunctionIntro hseed
    (Context.conjunctionIntro (Context.conjunctionLeft hmixed)
      (Context.conjunctionIntro (Context.conjunctionRight hmixed) hpath))
  exact .mp h2 (.mp h1 (.mp hd2 (.mp hd1
    (.mp hbranches (.mp hspan (.closed seeded_span_order_point))))))

theorem seeded_span_order_from_mixed_certificate (sourceCut targetCut : Nat) :
    theoremCode (certificate (seeded_span_order_from_mixed sourceCut targetCut)) =
      imp seededSpan.encode (imp (mixedPremises sourceCut targetCut)
        (imp seedSeed (imp pathPath (imp (both (member 0 2) (member 8 3))
          (imp (both (member 0 26) (member 8 27)) (imp (graphFormula 9 2 3).encode
            (imp (graphFormula 9 26 27).encode comparison))))))) :=
  certificate_correct (seeded_span_order_from_mixed sourceCut targetCut)

end PASoundness.PAtoCompactSeededSpanOrderMixedAssembly

#print axioms PASoundness.PAtoCompactSeededSpanOrderMixedAssembly.seedSeed
#print axioms PASoundness.PAtoCompactSeededSpanOrderMixedAssembly.pathPath
#print axioms PASoundness.PAtoCompactSeededSpanOrderMixedAssembly.seeded_span_order_from_mixed
#print axioms PASoundness.PAtoCompactSeededSpanOrderMixedAssembly.seeded_span_order_from_mixed_certificate
