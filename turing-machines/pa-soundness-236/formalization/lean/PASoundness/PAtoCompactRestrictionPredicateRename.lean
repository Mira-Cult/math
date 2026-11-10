import PASoundness.PAtoCompactGraphRestriction

/-! Exact named-syntax renaming for an endpoint-filter predicate.
This is a formula identity, not an edge or isomorphism derivation. -/
namespace PASoundness.PAtoCompactRestrictionPredicateRename
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactGraphRestriction

private def namedIff (a b : CompactNamed.Formula) : CompactNamed.Formula :=
  namedBoth (.imp a b) (.imp b a)

private def pairExpanded (p a b : Nat) : CompactNamed.Formula :=
  .ex 20 (.ex 21 (namedBoth
    (.all 22 (namedIff (.member 20 22) (.equal 22 a)))
    (namedBoth (.all 22 (namedIff (.member 21 22) (namedEither (.equal 22 a) (.equal 22 b))))
      (.all 22 (namedIff (.member p 22) (namedEither (.equal 22 20) (.equal 22 21)))))))

private theorem pair_expanded (p a b : Nat) : pairFormula p a b = pairExpanded p a b := rfl

/-- Changing the edge test name to 19 preserves the intended endpoint
predicate when the old test name avoids the endpoint parameters and all
internally bound pair and endpoint witness labels. -/
theorem rename_edge_to_graph_witness (t x y : Nat)
    (htx : t ≠ x) (hty : t ≠ y)
    (ht20 : t ≠ 20) (ht21 : t ≠ 21) (ht22 : t ≠ 22)
    (ht25 : t ≠ 25) (ht26 : t ≠ 26) :
    CompactNamed.replace t 19 (edgePredicate t x y) = edgePredicate 19 x y := by
  simp [edgePredicate, pair_expanded, pairExpanded, namedIff, namedBoth, namedEither,
    CompactNamed.replace, CompactNamed.rename, Ne.symm htx, Ne.symm hty,
    Ne.symm ht20, Ne.symm ht21, Ne.symm ht22, Ne.symm ht25, Ne.symm ht26]

end PASoundness.PAtoCompactRestrictionPredicateRename

#print axioms PASoundness.PAtoCompactRestrictionPredicateRename.rename_edge_to_graph_witness
