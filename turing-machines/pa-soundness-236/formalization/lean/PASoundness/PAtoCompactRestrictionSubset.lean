import PASoundness.PAtoCompactLeastCounterexample
import PASoundness.PAtoCompactGreatestDownward

/-! A pointwise K proof that a filtered graph is contained in its source.
The filter predicate is arbitrary; no graph existence or endpoint property
is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictionSubset
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFilteredSubset

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Instantiating the subset consequence of a literal filter graph gives an
actual finite K derivation. The filter binder t must differ from the source,
filtered output, and tested member names; their interpreted values may agree. -/
def filter_member_source (g h t P q : Nat)
    (htq : t ≠ q) (hth : t ≠ h) (htg : t ≠ g) :
    KDerivation (imp (filterGraph g h t P) (imp (member h q) (member g q))) := by
  exact compose
    (PAtoCompactLeastCounterexample.filter_graph_subset g h t P)
    (PAtoCompactGreatestDownward.subset_instance h g t q htq hth htg)

theorem filter_member_source_certificate (g h t P q : Nat)
    (htq : t ≠ q) (hth : t ≠ h) (htg : t ≠ g) :
    theoremCode (certificate (filter_member_source g h t P q htq hth htg)) =
      imp (filterGraph g h t P) (imp (member h q) (member g q)) :=
  certificate_correct (filter_member_source g h t P q htq hth htg)

end PASoundness.PAtoCompactRestrictionSubset

#print axioms PASoundness.PAtoCompactRestrictionSubset.filter_member_source
#print axioms PASoundness.PAtoCompactRestrictionSubset.filter_member_source_certificate
