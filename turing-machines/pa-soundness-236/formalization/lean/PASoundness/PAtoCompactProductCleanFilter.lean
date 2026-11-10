import PASoundness.PAtoCompactFilterInstantiation
import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.CompactQuantifiers

/-! A selector filter for a product graph: every retained set member is a
nested ordered pair whose three endpoints lie in the old product domains.
This is literal finite K proof data, not a multiplication totality theorem.
In particular, obtaining the filtered graph does not by itself prove that
all valid triples are retained as graph edges. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductCleanFilter
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Element `t` is a nested pair `((a,b),c)` whose endpoints are in the
respective input and output sets 0, 1, and 2 when `t` avoids the internal
binders 20–22 and 50–53. Pair witnesses are relational; no endpoint
inequality or extensionality hypothesis is assumed. -/
def cleanPredicate (t : Nat) : Formula :=
  .ex 50 (namedBoth (.member 0 50) (.ex 51 (namedBoth (.member 1 51)
    (.ex 52 (namedBoth (.member 2 52) (.ex 53
      (namedBoth (pairFormula 53 50 51) (pairFormula t 53 52))))))))

def filterCode (h : Nat) : Nat := filterGraph 6 h 55 (cleanPredicate 55).encode

/-- The literal selector output, before alpha-renaming its bound label. -/
def selectorName : Nat := filterPredicate 6 55 (cleanPredicate 55).encode

theorem selector_large : 55 < selectorName :=
  (filterPredicate_bounds 6 55 (cleanPredicate 55).encode).2.1

/-- K constructs the exact filtered graph at its selector-allocated name. -/
def product_filter_exists_selector : KDerivation (existsCode selectorName (filterCode selectorName)) := by
  exact filtered_subset_exists 6 55 (cleanPredicate 55).encode (by decide)

theorem product_filter_exists_selector_certificate :
    theoremCode (certificate product_filter_exists_selector) =
      existsCode selectorName (filterCode selectorName) :=
  certificate_correct product_filter_exists_selector

/-- A retained set member was present in the old graph and satisfies the
literal nested-pair predicate. The concrete element name is 19, the graph
witness name used in `graphFormula`. -/
def filter_at_graph_witness : KDerivation (imp (filterCode 54)
    (both (imp (member 54 19) (both (member 6 19) (cleanPredicate 19).encode))
      (imp (both (member 6 19) (cleanPredicate 19).encode) (member 54 19)))) := by
  have h := filter_at 6 54 55 19 (cleanPredicate 55) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hr : replace 55 19 (cleanPredicate 55) = cleanPredicate 19 := by decide
  rw [hr] at h
  exact h

theorem filter_at_graph_witness_certificate :
    theoremCode (certificate filter_at_graph_witness) =
      imp (filterCode 54)
        (both (imp (member 54 19) (both (member 6 19) (cleanPredicate 19).encode))
          (imp (both (member 6 19) (cleanPredicate 19).encode) (member 54 19))) :=
  certificate_correct filter_at_graph_witness
end PASoundness.PAtoCompactProductCleanFilter
#print axioms PASoundness.PAtoCompactProductCleanFilter.product_filter_exists_selector
#print axioms PASoundness.PAtoCompactProductCleanFilter.product_filter_exists_selector_certificate
#print axioms PASoundness.PAtoCompactProductCleanFilter.filter_at_graph_witness
#print axioms PASoundness.PAtoCompactProductCleanFilter.filter_at_graph_witness_certificate
