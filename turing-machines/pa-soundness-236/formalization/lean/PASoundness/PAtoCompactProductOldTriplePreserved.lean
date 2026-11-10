import PASoundness.PAtoCompactPartialInverseOldEdge
import PASoundness.PAtoCompactMultiplicationCandidate

/-! A literal K transport for an old product triple under the row invariant's
old-graph inclusion. It preserves the same nested-pair witness, without
assuming uniqueness of pair representations. This does not prove product
coverage, uniqueness, graph extension, or multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOldTriplePreserved
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPartialInverseOldEdge
open PASoundness.PAtoCompactZeroSuccessor
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private def inclusion : Formula := .all 9 (.imp (.member 10 9) (.member 64 9))
private def body : Formula := .imp (.member 10 9) (.member 64 9)
private def triple (g : Nat) : Formula := .ex 18
  (namedBoth (pairFormula 18 3 4) (graphFormula g 18 5))

/-- The old-inclusion predicate, instantiated at the graph's pair witness,
implies edge preservation with the identical pair witness. -/
def graph_edge_preserved : KDerivation (imp inclusion.encode
    (imp (graphFormula 10 18 5).encode (graphFormula 64 18 5).encode)) := by
  have ha := (universalAlpha 9 19 body (by decide) (by decide) (by decide)).1
  have hi : KDerivation (imp inclusion.encode (allCode 19 (imp (member 10 19) (member 64 19)))) := by
    simpa [inclusion,body,Formula.encode,replace,rename] using ha
  exact compose hi (graph_edge_monotone 10 64 18 5)

/-- Every old product triple at the displayed coordinate names survives in
the extended graph. The raw old-graph inclusion is the only antecedent. -/
def triple_preserved : KDerivation (imp inclusion.encode
    (imp (triple 10).encode (triple 64).encode)) := by
  let A := inclusion.encode
  let P := (pairFormula 18 3 4).encode
  let G := (graphFormula 10 18 5).encode
  let H := (graphFormula 64 18 5).encode
  have hpoint : KDerivation (imp A (imp (both P G) (both P H))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [both P G,A]
    have h : Context Γ (both P G) := .head _ _
    have ha : Context Γ A := .hypothesis (by simp [Γ])
    have hp : Context Γ P := Context.conjunctionLeft h
    have hg : Context Γ G := Context.conjunctionRight h
    have hh : Context Γ H := .mp hg (.mp ha (.closed graph_edge_preserved))
    exact Context.conjunctionIntro hp hh
  have hv : KDerivation (imp A (allCode 18 A)) := inclusion.vacuity 18 (by decide)
  have h := conditionalExistsCongr 18 hv hpoint
  simpa [triple,A,P,G,H,namedBoth,Formula.not,Formula.encode,both,neg] using h

theorem triple_preserved_certificate : theoremCode (certificate triple_preserved) =
    imp inclusion.encode (imp (triple 10).encode (triple 64).encode) :=
  certificate_correct triple_preserved
end PASoundness.PAtoCompactProductOldTriplePreserved
#print axioms PASoundness.PAtoCompactProductOldTriplePreserved.graph_edge_preserved
#print axioms PASoundness.PAtoCompactProductOldTriplePreserved.triple_preserved
#print axioms PASoundness.PAtoCompactProductOldTriplePreserved.triple_preserved_certificate
