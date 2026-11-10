import PASoundness.PAtoCompactPairAll

/-! Freshness of the automatically selected unordered-pair labels. These
are arithmetic facts about syntax names, not assertions about object values. -/
namespace PASoundness.PAtoCompactPairAllFresh
open PASoundness.PAtoCompactPairAll PASoundness.PAtoCompactPairFresh
open PASoundness.PAtoCompactPairSelector PASoundness.PAtoCompactSingletonSelector

/-- Both generated binders avoid the endpoints and each other, even when the
endpoint names coincide. -/
theorem pair_names_fresh (a b : Nat) :
    testName a b ≠ a ∧ testName a b ≠ b ∧
    witnessName a b ≠ a ∧ witnessName a b ≠ b ∧ witnessName a b ≠ testName a b := by
  by_cases h : a = b
  · subst b
    have hc := PAtoCompactSingletonSelector.predicate_names_lt a (a+1)
    simp only [testName,witnessName,if_true]
    omega
  · have hc := PAtoCompactPairSelector.predicate_names_lt a b (point a b)
    have hs := PAtoCompactSingletonSelector.predicate_names_lt a (point a b)
    simp only [testName,witnessName,h,if_false,pairName,singletonName,pairTest,
      singleTest,pairWitness,singletonWitness]
    omega

end PASoundness.PAtoCompactPairAllFresh

#print axioms PASoundness.PAtoCompactPairAllFresh.pair_names_fresh
