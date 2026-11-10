import PASoundness.PAtoCompactFilteredSubset

/-! Selector-8 suffix filtering for the proposed addition relation.

The K theorem constructs a subset of a supplied result object using literal
compact negation, which is implication to code 1. Its ordinary set-difference
reading is proved only in standard HF semantics, where code 1 is false; no
K quotient, arithmetic axiom, or PA proof transport is asserted. -/
set_option maxRecDepth 65536
namespace PASoundness.PAtoCompactAdditionSuffix
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactMatrix PASoundness.CompactSemantics
open PASoundness.PAtoCompactFilteredSubset

/-- The predicate-code witness selected for the part of `z` outside `cut`. -/
def suffixWitness (z cut t : Nat) : Nat :=
  filterPredicate z t (neg (member cut t))

/-- The selector-chosen name is distinct from both input names and the test
binder; it is generated from the exact literal predicate. -/
theorem suffixWitness_bounds (z cut t : Nat) :
    z < suffixWitness z cut t ∧ cut < suffixWitness z cut t ∧
      t < suffixWitness z cut t := by
  have h := filterPredicate_bounds z t (neg (member cut t))
  have hp := Cantor.left_le_pair cut t
  have hn := Cantor.left_le_pair (member cut t) 1
  have hc : cut < neg (member cut t) := by
    unfold neg imp member at *
    omega
  unfold suffixWitness
  exact ⟨h.1, Nat.lt_trans hc h.2.2, h.2.1⟩

/-- Selector 8 constructs the exact literal filtered suffix. The test label
must differ from both free inputs for the stated intended binding. -/
def suffix_exists (z cut t : Nat) (hzt : z ≠ t) (_hct : cut ≠ t) :
    KDerivation (existsCode (suffixWitness z cut t)
      (filterGraph z (suffixWitness z cut t) t (neg (member cut t)))) :=
  filtered_subset_exists z t (neg (member cut t)) hzt

theorem suffix_exists_certificate (z cut t : Nat) (hzt : z ≠ t) (hct : cut ≠ t) :
    theoremCode (certificate (suffix_exists z cut t hzt hct)) =
      existsCode (suffixWitness z cut t)
        (filterGraph z (suffixWitness z cut t) t (neg (member cut t))) :=
  certificate_correct (suffix_exists z cut t hzt hct)

/-- In the standard HF structure, this same literal existential asserts that
some code has exactly the members of `z` that are not members of `cut`. -/
theorem suffix_standard (z cut t : Nat) (ρ : Environment)
    (hzt : z ≠ t) (hct : cut ≠ t) :
    (decode (existsCode (suffixWitness z cut t)
      (filterGraph z (suffixWitness z cut t) t (neg (member cut t))))).Realize ρ ↔
    ∃ w, ∀ v, bit w v = true ↔
      bit (ρ z) v = true ∧ bit (ρ cut) v = false := by
  rw [show suffixWitness z cut t = filterPredicate z t (neg (member cut t)) by rfl]
  rw [filtered_subset_standard z t (neg (member cut t)) ρ hzt]
  apply exists_congr
  intro w
  apply forall_congr'
  intro v
  simp [realize_neg, realize_member, update_other ρ t cut v hct, update_same]

end PASoundness.PAtoCompactAdditionSuffix

#print axioms PASoundness.PAtoCompactAdditionSuffix.suffix_exists
#print axioms PASoundness.PAtoCompactAdditionSuffix.suffix_exists_certificate
#print axioms PASoundness.PAtoCompactAdditionSuffix.suffix_standard
