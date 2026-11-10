import PASoundness.PAtoCompactPointAdjoin
import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactTransitiveWitness

/-! Preservation of an old inverse-graph edge under an explicitly supplied
point-adjunction graph. This is one local successor-invariant component; it
does not handle new endpoint edges, spurious edges, or graph construction. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseOldEdge
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactTransitiveWitness
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- An adjoined graph contains every old graph entry, at the fixed pair-witness
name 19. Names 7,9,11,14 and 19 are pairwise distinct. -/
def adjoin_old_entry : KDerivation
    (imp (adjoinCode 7 11 9 14) (allCode 19 (imp (member 7 19) (member 9 19)))) := by
  let E := either (equal 14 11) (member 7 14)
  let B := both (imp (member 9 14) E) (imp E (member 9 14))
  have hp : KDerivation (imp B (imp (member 7 14) (member 9 14))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [member 7 14,B]
    have hm : Context Γ (member 7 14) := Context.head _ _
    have hb : Context Γ B := .hypothesis (by simp [Γ])
    have he : Context Γ E := Context.disjunctionRight (a := equal 14 11) hm
    exact .mp he (Context.conjunctionRight hb)
  have hall : KDerivation (imp (adjoinCode 7 11 9 14)
      (allCode 14 (imp (member 7 14) (member 9 14)))) := allCongr 14 hp
  let f : Formula := .imp (.member 7 14) (.member 9 14)
  have ha := (universalAlpha 14 19 f (by decide) (by decide) (by decide)).1
  have ha' : KDerivation (imp (allCode 14 (imp (member 7 14) (member 9 14)))
      (allCode 19 (imp (member 7 19) (member 9 19)))) := by
    simpa [f, Formula.encode, replace, rename] using ha
  exact compose hall ha'

/-- Graph inclusion preserves an encoded edge for arbitrary literal coordinate
names; callers must separately ensure their intended graph-binder freshness. -/
def graph_edge_monotone (g h a b : Nat) : KDerivation
    (imp (allCode 19 (imp (member g 19) (member h 19)))
      (imp (graphFormula g a b).encode (graphFormula h a b).encode)) := by
  let M := member g 19
  let N := member h 19
  let P := (pairFormula 19 a b).encode
  let H := allCode 19 (imp M N)
  let A := both M P
  let B := both N P
  have hlocal : KDerivation (imp (imp M N) (imp A B)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [A,imp M N]
    have ha : Context Γ A := Context.head _ _
    have hi : Context Γ (imp M N) := .hypothesis (by simp [Γ])
    exact Context.conjunctionIntro (.mp (Context.conjunctionLeft ha) hi)
      (Context.conjunctionRight ha)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula g a b).encode,H]
  have hh : Context Γ H := .hypothesis (by simp [Γ])
  have hg : Context Γ (graphFormula g a b).encode := Context.head _ _
  have hall : Context Γ (allCode 19 (imp A B)) :=
    Context.allMP hh (.closed (.generalize 19 hlocal))
  have hex : Context Γ (existsCode 19 A) := hg
  have hnew : Context Γ (existsCode 19 B) := exists_map_context hall hex
  exact hnew

/-- Every old inverse edge remains present after the point is adjoined. -/
def adjoin_preserves_edge : KDerivation
    (imp (adjoinCode 7 11 9 14)
      (imp (graphFormula 7 3 2).encode (graphFormula 9 3 2).encode)) :=
  compose adjoin_old_entry (graph_edge_monotone 7 9 3 2)

def oldPrefixRhs : Nat := both (member 8 2) (graphFormula 6 2 3).encode

/-- If the old partial invariant supplies coverage of an old-prefix pair,
the point-adjoined graph still covers that pair. The coverage implication
and point-adjunction are explicit assumptions. -/
def retain_old_prefix_coverage : KDerivation
    (imp (adjoinCode 7 11 9 14)
      (imp (imp oldPrefixRhs (graphFormula 7 3 2).encode)
        (imp oldPrefixRhs (graphFormula 9 3 2).encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldPrefixRhs,imp oldPrefixRhs (graphFormula 7 3 2).encode,
    adjoinCode 7 11 9 14]
  have hp : Context Γ oldPrefixRhs := Context.head _ _
  have hc : Context Γ (imp oldPrefixRhs (graphFormula 7 3 2).encode) :=
    .hypothesis (by simp [Γ])
  have ha : Context Γ (adjoinCode 7 11 9 14) := .hypothesis (by simp [Γ])
  exact .mp (.mp hp hc) (.mp ha (.closed adjoin_preserves_edge))

theorem retain_old_prefix_coverage_certificate :
    theoremCode (certificate retain_old_prefix_coverage) =
      imp (adjoinCode 7 11 9 14)
        (imp (imp oldPrefixRhs (graphFormula 7 3 2).encode)
          (imp oldPrefixRhs (graphFormula 9 3 2).encode)) :=
  certificate_correct retain_old_prefix_coverage

end PASoundness.PAtoCompactPartialInverseOldEdge

#print axioms PASoundness.PAtoCompactPartialInverseOldEdge.adjoin_preserves_edge
#print axioms PASoundness.PAtoCompactPartialInverseOldEdge.retain_old_prefix_coverage
#print axioms PASoundness.PAtoCompactPartialInverseOldEdge.retain_old_prefix_coverage_certificate
