import PASoundness.PAtoCompactGraphAdjoinPreserve
import PASoundness.PAtoCompactMultiplicationCandidate

/-! Pointwise preservation of a multiplication-style triple edge when a
single object is adjoined to its graph. This is not row collection, product
existence, arithmetic induction, or PA proof transport. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationTripleAdjoinPreserve
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactGraphAdjoinPreserve PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveWitness
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The product-style graph triple with explicit graph and coordinate labels.
Name 18 is the nested-pair witness, and graph/pair binders are 19–22. -/
def tripleAt (g a b c : Nat) : Formula := .ex 18
  (namedBoth (pairFormula 18 a b) (graphFormula g 18 c))

/-- For one arbitrary old product-style triple, the graph obtained by
adjoining point 12 to graph 6 retains that triple. The literal coordinate
labels are 3,4,5, and 16 is the adjoin graph's test binder. -/
def triple_preserved : KDerivation
    (imp (adjoinCode 6 12 9 16)
      (imp (tripleAt 6 3 4 5).encode (tripleAt 9 3 4 5).encode)) := by
  let A := adjoinCode 6 12 9 16
  let P := (pairFormula 18 3 4).encode
  let G := (graphFormula 6 18 5).encode
  let H := (graphFormula 9 18 5).encode
  let I := both P G
  let J := both P H
  let Γ := [A]
  have ha : Context Γ A := .head _ _
  have hs : Context Γ (imp I J) := by
    apply Context.deduction
    let Δ := [I,A]
    have hi : Context Δ I := .head _ _
    have hp : Context Δ P := Context.conjunctionLeft hi
    have hg : Context Δ G := Context.conjunctionRight hi
    have hA : Context Δ A := .under ha _
    have hh : Context Δ H := .mp hg (.mp hA (.closed
      (adjoin_preserves_edge 6 12 9 16 18 5 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))))
    exact Context.conjunctionIntro hp hh
  let af : Formula := namedAdjoin 6 12 9 16
  have hvA : KDerivation (imp A (allCode 18 A)) := by
    have h := af.vacuity 18 (by decide)
    simpa [af,A,adjoinCode,namedAdjoin,namedBoth,namedEither,Formula.encode,
      CompactProof.both,CompactProof.neg,CompactDerivations.either] using h
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 18 h)) := by
    intro h hh
    have he : h = A := by simpa [Γ] using hh
    subst h
    exact hvA
  have hall : Context Γ (allCode 18 (imp I J)) := Context.generalize 18 hv hs
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Δ := [(tripleAt 6 3 4 5).encode,A]
  have he : Context Δ (existsCode 18 I) := by
    simpa [Δ, tripleAt, I, P, G, namedBoth, Formula.not, Formula.encode,
      CompactProof.both, CompactProof.neg] using (Context.head [A] (tripleAt 6 3 4 5).encode)
  have hall' : Context Δ (allCode 18 (imp I J)) := Context.weaken hall (by
    intro x hx
    have heq : x = A := by simpa [Γ] using hx
    subst x
    simp [Δ])
  have hout : Context Δ (existsCode 18 J) := exists_map_context hall' he
  simpa [Δ, A, tripleAt, J, P, H, namedBoth, Formula.not, Formula.encode,
    CompactProof.both, CompactProof.neg] using hout

theorem triple_preserved_certificate :
    theoremCode (certificate triple_preserved) =
      imp (adjoinCode 6 12 9 16)
        (imp (tripleAt 6 3 4 5).encode (tripleAt 9 3 4 5).encode) :=
  certificate_correct triple_preserved
end PASoundness.PAtoCompactMultiplicationTripleAdjoinPreserve
#print axioms PASoundness.PAtoCompactMultiplicationTripleAdjoinPreserve.triple_preserved
#print axioms PASoundness.PAtoCompactMultiplicationTripleAdjoinPreserve.triple_preserved_certificate
