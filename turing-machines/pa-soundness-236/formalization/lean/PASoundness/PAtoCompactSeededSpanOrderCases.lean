import PASoundness.PAtoCompactSeededSpanOrderSplit

/-! Pointwise four-case order assembly for a seeded common-source span. The
two actual output edges are split using the supplied invariant. The four
branch comparison proofs remain explicit K antecedents. -/
namespace PASoundness.PAtoCompactSeededSpanOrderCases

open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactSeededSpanBase
open PASoundness.PAtoCompactCommonSourceSpanBase PASoundness.PAtoCompactSeededSpanOrderSplit

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def comparison : Nat := both (imp (member 26 2) (member 27 3))
  (imp (member 27 3) (member 26 2))
def firstSeed : Nat := (graphFormula 14 2 3).encode
def secondSeed : Nat := (graphFormula 14 26 27).encode
def firstPath : Nat := spanPath.encode
def secondPath : Nat := movedPath.encode
def branches : Nat := both (imp firstSeed (imp secondSeed comparison))
  (both (imp firstSeed (imp secondPath comparison))
    (both (imp firstPath (imp secondSeed comparison))
      (imp firstPath (imp secondPath comparison))))

/-- For two supplied graph-9 edges with actual endpoint membership, the four
displayed seed/path branch implications suffice for order agreement. -/
def seeded_span_order_point : KDerivation (imp seededSpan.encode (imp branches
    (imp (both (member 0 2) (member 8 3))
      (imp (both (member 0 26) (member 8 27))
        (imp (graphFormula 9 2 3).encode
          (imp (graphFormula 9 26 27).encode comparison)))))) := by
  apply Context.closeEmpty
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
  let Γ := [H2,H1,D2,D1,branches,seededSpan.encode]
  have hs : Context Γ seededSpan.encode := .hypothesis (by simp [Γ])
  have hd1 : Context Γ D1 := .hypothesis (by simp [Γ])
  have hd2 : Context Γ D2 := .hypothesis (by simp [Γ])
  have he1 : Context Γ H1 := .hypothesis (by simp [Γ])
  have he2 : Context Γ H2 := .head _ _
  have hsplit1 : Context Γ (either firstSeed firstPath) :=
    .mp he1 (.mp hd1 (.mp hs (.closed first_edge_split)))
  have hsplit2 : Context Γ (either secondSeed secondPath) :=
    .mp he2 (.mp hd2 (.mp hs (.closed second_edge_split)))
  apply Context.disjunctionElim hsplit1
  · have hsplit2' := Context.under hsplit2 firstSeed
    apply Context.disjunctionElim hsplit2'
    · let Δ := secondSeed :: firstSeed :: Γ
      have hb : Context Δ branches := .hypothesis (by simp [Δ,Γ])
      have h1 : Context Δ firstSeed := .hypothesis (by simp [Δ])
      have h2 : Context Δ secondSeed := .head _ _
      exact .mp h2 (.mp h1 (Context.conjunctionLeft hb))
    · let Δ := secondPath :: firstSeed :: Γ
      have hb : Context Δ branches := .hypothesis (by simp [Δ,Γ])
      have h1 : Context Δ firstSeed := .hypothesis (by simp [Δ])
      have h2 : Context Δ secondPath := .head _ _
      exact .mp h2 (.mp h1 (Context.conjunctionLeft (Context.conjunctionRight hb)))
  · have hsplit2' := Context.under hsplit2 firstPath
    apply Context.disjunctionElim hsplit2'
    · let Δ := secondSeed :: firstPath :: Γ
      have hb : Context Δ branches := .hypothesis (by simp [Δ,Γ])
      have h1 : Context Δ firstPath := .hypothesis (by simp [Δ])
      have h2 : Context Δ secondSeed := .head _ _
      exact .mp h2 (.mp h1 (Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hb))))
    · let Δ := secondPath :: firstPath :: Γ
      have hb : Context Δ branches := .hypothesis (by simp [Δ,Γ])
      have h1 : Context Δ firstPath := .hypothesis (by simp [Δ])
      have h2 : Context Δ secondPath := .head _ _
      exact .mp h2 (.mp h1 (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hb))))

theorem seeded_span_order_point_certificate : theoremCode (certificate seeded_span_order_point) =
    imp seededSpan.encode (imp branches (imp (both (member 0 2) (member 8 3))
      (imp (both (member 0 26) (member 8 27)) (imp (graphFormula 9 2 3).encode
        (imp (graphFormula 9 26 27).encode comparison))))) :=
  certificate_correct seeded_span_order_point

end PASoundness.PAtoCompactSeededSpanOrderCases

#print axioms PASoundness.PAtoCompactSeededSpanOrderCases.comparison
#print axioms PASoundness.PAtoCompactSeededSpanOrderCases.firstSeed
#print axioms PASoundness.PAtoCompactSeededSpanOrderCases.secondSeed
#print axioms PASoundness.PAtoCompactSeededSpanOrderCases.firstPath
#print axioms PASoundness.PAtoCompactSeededSpanOrderCases.secondPath
#print axioms PASoundness.PAtoCompactSeededSpanOrderCases.branches
#print axioms PASoundness.PAtoCompactSeededSpanOrderCases.seeded_span_order_point
#print axioms PASoundness.PAtoCompactSeededSpanOrderCases.seeded_span_order_point_certificate
