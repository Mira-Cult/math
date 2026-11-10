import PASoundness.PAtoCompactTransitiveDomain

/-! Exact standard-HF reading of the proposed one-level transitivity
condition. This is semantic analysis, not an internal K domain proof. -/
namespace PASoundness.PAtoCompactTransitiveSemantics
open PASoundness.CompactMatrix PASoundness.CompactSemantics
open PASoundness.CompactProof PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactTransitiveDomain

/-- The binary-code transitivity condition in standard HF. -/
def transHF (x : Nat) : Prop :=
  ∀ a b, bit x a = true → bit a b = true → bit x b = true

/-- The displayed named K code means transitivity of x and transitivity of
every member, in the standard HF interpretation under fresh binders. -/
theorem one_level_meaning (x b p q : Nat) (ρ : Environment)
    (fresh : [x,b,p,q].Nodup) :
    (decode (oneLevelTransitiveCode x b p q)).Realize ρ ↔
      transHF (ρ x) ∧ ∀ a, bit (ρ x) a = true → transHF a := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, not_false_eq_true] at fresh
  simp only [oneLevelTransitiveCode, membersTransitiveCode, transitiveCode,
    realize_both, realize_all, realize_imp, realize_member]
  simp_all [transHF, update, Ne.symm]

end PASoundness.PAtoCompactTransitiveSemantics

#print axioms PASoundness.PAtoCompactTransitiveSemantics.one_level_meaning
