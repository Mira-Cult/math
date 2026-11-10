import PASoundness.PAtoCompactFilteredSubset

/-! Selector 8 constructs the exact intersection graph used by the
least-subset successor argument. The selector-chosen witness name is the code
of the filtered predicate; numeric bounds make its freshness explicit. This
does not assert successor closure or an arithmetic interpretation. -/
set_option maxRecDepth 65536
namespace PASoundness.PAtoCompactIntersectionExists
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFilteredSubset

/-- Literal selector-chosen intersection witness name. -/
def intersectionWitness (u x q : Nat) : Nat := filterPredicate u q (member x q)

/-- The chosen witness name is fresh for both sets and the test name. -/
theorem intersectionWitness_bounds (u x q : Nat) :
    u < intersectionWitness u x q ∧ x < intersectionWitness u x q ∧
    q < intersectionWitness u x q := by
  have h := filterPredicate_bounds u q (member x q)
  have hx := Cantor.left_le_pair x q
  have hp : x < member x q := by
    unfold member
    omega
  unfold intersectionWitness
  exact ⟨h.1, Nat.lt_trans hp h.2.2, h.2.1⟩

/-- Any name at most the test binder is distinct from the chosen witness. -/
theorem witness_fresh_of_le (u x q z : Nat) (hz : z ≤ q) :
    intersectionWitness u x q ≠ z := by
  have h := (intersectionWitness_bounds u x q).2.2
  omega

/-- A K proof constructs a represented intersection of u and x. The output
binder is the literal selector witness, not an arbitrary preselected name.
The second freshness condition ensures that the binder q does not shadow x
in the intended intersection graph. -/
def intersection_exists (u x q : Nat) (huq : u ≠ q) (_hxq : x ≠ q) :
    KDerivation (existsCode (intersectionWitness u x q)
      (filterGraph u (intersectionWitness u x q) q (member x q))) :=
  filtered_subset_exists u q (member x q) huq

theorem intersection_exists_certificate (u x q : Nat) (huq : u ≠ q) (hxq : x ≠ q) :
    theoremCode (certificate (intersection_exists u x q huq hxq)) =
      existsCode (intersectionWitness u x q)
        (filterGraph u (intersectionWitness u x q) q (member x q)) :=
  certificate_correct (intersection_exists u x q huq hxq)

end PASoundness.PAtoCompactIntersectionExists

#print axioms PASoundness.PAtoCompactIntersectionExists.intersection_exists
#print axioms PASoundness.PAtoCompactIntersectionExists.intersection_exists_certificate
