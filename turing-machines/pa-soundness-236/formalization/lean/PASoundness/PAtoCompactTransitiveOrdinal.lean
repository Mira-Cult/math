import PASoundness.HFCoding
import PASoundness.PAtoCompactOrdinalMax

/-! Standard-HF transitive-set/ordinal characterization. This is external
semantics, not an internal K domain-exhaustion or arithmetic-interpretation
argument. -/
namespace PASoundness.PAtoCompactTransitiveOrdinal
open PASoundness.HFCoding

/-- Membership induction reduces the characterization to the finite
maximum-member lemma, supplied explicitly here. -/
theorem transitive_members_ordinal_of_max
    (hmax : ∀ x : Object,
      (∀ a, a ∈ x → ∀ b, b ∈ a → b ∈ x) →
      (∀ a, a ∈ x → ∃ n, a = ordinal n) → ∃ n, x = ordinal n)
    (x : Object) :
    (∀ a, a ∈ x → ∀ b, b ∈ a → b ∈ x) →
    (∀ a, a ∈ x → ∀ b, b ∈ a → ∀ c, c ∈ b → c ∈ a) →
    ∃ n, x = ordinal n := by
  induction x using membership_wellFounded.induction with
  | h x ih =>
    intro hx hm
    apply hmax x hx
    intro a ha
    apply ih a ha
    · exact hm a ha
    · intro b hb
      exact hm b (hx a ha b hb)

/-- Every standard-HF transitive object all of whose members are transitive
is a finite ordinal. No least/greatest-subset premise is needed here. -/
theorem transitive_members_ordinal (x : Object)
    (hx : ∀ a, a ∈ x → ∀ b, b ∈ a → b ∈ x)
    (hm : ∀ a, a ∈ x → ∀ b, b ∈ a → ∀ c, c ∈ b → c ∈ a) :
    ∃ n, x = ordinal n :=
  transitive_members_ordinal_of_max
    PASoundness.PAtoCompactOrdinalMax.transitive_ordinal_members x hx hm

end PASoundness.PAtoCompactTransitiveOrdinal

#print axioms PASoundness.PAtoCompactTransitiveOrdinal.transitive_members_ordinal_of_max
#print axioms PASoundness.PAtoCompactTransitiveOrdinal.transitive_members_ordinal
