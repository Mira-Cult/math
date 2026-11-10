import PASoundness.PAtoCompactPointAdjoin
import PASoundness.PAtoCompactTransitiveWitness
import PASoundness.PAtoCompactOrderIsomorphism

/-! A K graph obtained by adjoining one point retains every existing graph
edge. This uses the exact existential pair witnesses and does not assert
collection, quotient congruence, identity graphs, or PA interpretation. -/
set_option maxRecDepth 65536
namespace PASoundness.PAtoCompactGraphAdjoinPreserve
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactTransitiveWitness PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- At a fresh test name, an adjoined set contains every old member. -/
def adjoin_preserves_row (g p h q v : Nat)
    (hqg : q ≠ g) (hqp : q ≠ p) (hqh : q ≠ h) (hqv : q ≠ v) :
    KDerivation (imp (adjoinCode g p h q) (imp (member g v) (member h v))) := by
  let f := namedBoth (.imp (.member h q) (namedEither (.equal q p) (.member g q)))
    (.imp (namedEither (.equal q p) (.member g q)) (.member h q))
  have hi := CompactNamed.universalInstance q v f hqv
    (by simp [f,namedBoth,namedEither,CompactNamed.Formula.binders])
    (by simp [f,namedBoth,namedEither,CompactNamed.Formula.binders])
  have hi' : KDerivation (imp (adjoinCode g p h q)
      (both (imp (member h v) (either (equal v p) (member g v)))
        (imp (either (equal v p) (member g v)) (member h v)))) := by
    simpa [f,adjoinCode,namedBoth,namedEither,CompactNamed.Formula.encode,
      CompactNamed.replace,CompactNamed.rename,CompactProof.both,CompactProof.neg,
      CompactDerivations.either,hqg,hqp,hqh,hqv,
      Ne.symm hqg,Ne.symm hqp,Ne.symm hqh,Ne.symm hqv] using hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member g v,adjoinCode g p h q]
  have hm : Context Γ (member g v) := Context.head _ _
  have ha : Context Γ (adjoinCode g p h q) := .hypothesis (by simp [Γ])
  have he : Context Γ (either (equal v p) (member g v)) := Context.disjunctionRight hm
  exact .mp he (Context.conjunctionRight (.mp ha (.closed hi')))

/-- Every exact graph edge remains present after adjoining a point. The name
19 is the bound pair-object witness in graphFormula and must be absent from
the free and bound labels of the supplied adjoin graph. -/
def adjoin_preserves_edge (g p h q a b : Nat)
    (hqg : q ≠ g) (hqp : q ≠ p) (hqh : q ≠ h)
    (h19g : 19 ≠ g) (h19p : 19 ≠ p) (h19h : 19 ≠ h) (h19q : 19 ≠ q) :
    KDerivation (imp (adjoinCode g p h q)
      (imp (graphFormula g a b).encode (graphFormula h a b).encode)) := by
  let A := adjoinCode g p h q
  let F := (pairFormula 19 a b).encode
  let I := both (member g 19) F
  let J := both (member h 19) F
  let Γ := [A]
  have ha : Context Γ A := Context.head [] A
  have hstep : Context Γ (imp I J) := by
    apply Context.deduction
    have hi : Context (I :: Γ) I := Context.head _ _
    have hm : Context (I :: Γ) (member g 19) := Context.conjunctionLeft hi
    have hf : Context (I :: Γ) F := Context.conjunctionRight hi
    have hnew : Context (I :: Γ) (member h 19) :=
      .mp hm (.mp (Context.under ha I) (.closed (adjoin_preserves_row g p h q 19
        hqg hqp hqh (Ne.symm h19q))))
    exact Context.conjunctionIntro hnew hf
  let f := namedAdjoin g p h q
  have hn : 19 ∉ f.names := by
    simp [f,namedAdjoin,namedBoth,namedEither,CompactNamed.Formula.names,
      h19g,h19p,h19h,h19q]
  have hvA : KDerivation (imp A (allCode 19 A)) := by
    have h := f.vacuity 19 hn
    simpa [f,A,namedAdjoin,namedBoth,namedEither,adjoinCode,CompactNamed.Formula.encode,
      CompactProof.both,CompactProof.neg,CompactDerivations.either] using h
  have hv : ∀ h', h' ∈ Γ → KDerivation (imp h' (allCode 19 h')) := by
    intro h' hh
    have he : h' = A := by simpa [Γ] using hh
    subst h'; exact hvA
  have hall : Context Γ (allCode 19 (imp I J)) := Context.generalize 19 hv hstep
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Δ := [(graphFormula g a b).encode,A]
  have hedge : Context Δ (graphFormula g a b).encode := Context.head _ _
  have hall' : Context Δ (allCode 19 (imp I J)) := Context.weaken hall (by
    intro x hx
    have he : x = A := by simpa [Γ] using hx
    subst x; simp [Δ])
  change Context Δ (existsCode 19 I) at hedge
  have hnew : Context Δ (existsCode 19 J) := exists_map_context hall' hedge
  change Context Δ (graphFormula h a b).encode at hnew
  exact hnew

theorem adjoin_preserves_edge_certificate (g p h q a b : Nat)
    (hqg : q ≠ g) (hqp : q ≠ p) (hqh : q ≠ h)
    (h19g : 19 ≠ g) (h19p : 19 ≠ p) (h19h : 19 ≠ h) (h19q : 19 ≠ q) :
    theoremCode (certificate (adjoin_preserves_edge g p h q a b
      hqg hqp hqh h19g h19p h19h h19q)) =
      imp (adjoinCode g p h q)
        (imp (graphFormula g a b).encode (graphFormula h a b).encode) :=
  certificate_correct (adjoin_preserves_edge g p h q a b hqg hqp hqh h19g h19p h19h h19q)

end PASoundness.PAtoCompactGraphAdjoinPreserve

#print axioms PASoundness.PAtoCompactGraphAdjoinPreserve.adjoin_preserves_edge
#print axioms PASoundness.PAtoCompactGraphAdjoinPreserve.adjoin_preserves_edge_certificate
