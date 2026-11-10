import PASoundness.CompactNamedSemantics

/-! A concrete first-order *candidate* for quotient equality on the proposed
ordinal-like K domain. It says that a represented graph of Kuratowski-pair
witnesses is an order isomorphism between the membership orders of two sets.
No equivalence, congruence, graph-existence or proof-translation theorem is
claimed here. In particular, K's bounded selector does not directly supply
arbitrary products or compositions of graphs. Named bottom encodes literal
`member 0 0`; the named-IR free-name calculation below is not by itself a
general semantic claim about bottom in arbitrary raw K models. -/
namespace PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.CompactNamed
open PASoundness.CompactMatrix (Environment bit bit_eq_testBit update)

private def conj (a b : Formula) : Formula := (a.imp b.not).not
private def disj (a b : Formula) : Formula := a.not.imp b
private def iff' (a b : Formula) : Formula := conj (a.imp b) (b.imp a)

/-- Relational Kuratowski pair: the members of p are exactly the selected
singleton of a and unordered pair of a and b. Those witnesses may coincide
and need not be unique objects in a nonextensional model. Names 20–22 are bound; this
reading requires p, a and b to differ from each of those labels. -/
def pairFormula (p a b : Nat) : Formula :=
  .ex 20 (.ex 21 (conj
    (.all 22 (iff' (.member 20 22) (.equal 22 a)))
    (conj (.all 22 (iff' (.member 21 22) (disj (.equal 22 a) (.equal 22 b))))
      (.all 22 (iff' (.member p 22) (disj (.equal 22 20) (.equal 22 21)))))))

/-- Some member of g is a relational pair of a and b. Names 19–22 are bound;
this reading requires g, a and b to differ from all four labels. The concrete
calls below satisfy these freshness conditions. -/
def graphFormula (g a b : Nat) : Formula :=
  .ex 19 (conj (.member g 19) (pairFormula 19 a b))

/-- Names 0 and 1 denote the input sets, 6 the graph. Every member of 0 has
exactly one image in 1, and every member of 1 exactly one preimage in 0. -/
def bijectionFormula : Formula := conj
  (.all 2 (.imp (.member 0 2) (.ex 3
    (conj (.member 1 3) (conj (graphFormula 6 2 3)
      (.all 4 (.imp (conj (.member 1 4) (graphFormula 6 2 4)) (.equal 4 3))))))))
  (.all 3 (.imp (.member 1 3) (.ex 2
    (conj (.member 0 2) (conj (graphFormula 6 2 3)
      (.all 4 (.imp (conj (.member 0 4) (graphFormula 6 4 3)) (.equal 4 2))))))))

/-- Membership is preserved and reflected by the selected graph on the
specified input and output sets. -/
def orderFormula : Formula :=
  .all 2 (.all 4 (.all 3 (.all 5
    (.imp (conj (.member 0 2) (conj (.member 0 4)
      (conj (.member 1 3) (conj (.member 1 5)
        (conj (graphFormula 6 2 3) (graphFormula 6 4 5))))))
      (iff' (.member 4 2) (.member 5 3))))))

/-- Concrete quotient-equality proposal; names 0 and 1 are its only free
names in the named syntax. This alone does not establish an interpretation. -/
def equivalentFormula : Formula := .ex 6 (conj bijectionFormula orderFormula)

theorem equivalent_free : equivalentFormula.free = {0,1} := by decide

/-- Standard-HF sanity check: the proposed formula relates the two empty
codes. This is not a K proof that the relation is reflexive or a quotient. -/
theorem standard_empty_equivalent (ρ : Environment) (h0 : ρ 0 = 0) (h1 : ρ 1 = 0) :
    equivalentFormula.Realize ρ := by
  have hf : ∀ v, bit 0 v = false := by intro v; simp [bit_eq_testBit]
  dsimp only [equivalentFormula, Formula.Realize]
  refine ⟨0, ?_⟩
  simp [conj, iff', bijectionFormula, orderFormula, Formula.not, Formula.Realize,
    update, h0, h1, hf]

end PASoundness.PAtoCompactOrderIsomorphism

#print axioms PASoundness.PAtoCompactOrderIsomorphism.equivalent_free
#print axioms PASoundness.PAtoCompactOrderIsomorphism.standard_empty_equivalent
