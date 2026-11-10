import PASoundness.PAtoCompactPairFilterBounds

/-! Fresh labels for the represented filtered-pair witness used in local
comparison. This helper is distinct from unordered-pair construction. -/
namespace PASoundness.PAtoCompactLocalPairFresh
open PASoundness.PAtoCompactPairFilter PASoundness.PAtoCompactPairFilterBounds

def testName (x a b : Nat) : Nat := x + a + b + 1

/-- The test label and the generated pair-witness successors are pairwise
fresh when the three visible names are pairwise distinct. -/
theorem pair_fresh_allocation (x a b : Nat) (fresh : [x,a,b].Nodup) :
    let t := testName x a b
    let c := pairWitness x t a b
    [x,t,a,b,c+1,c+2,c+3,c+4,c].Nodup := by
  dsimp only
  have hb := pair_witness_bounds x (testName x a b) a b
  have ht : x < testName x a b ∧ a < testName x a b ∧ b < testName x a b := by
    unfold testName
    omega
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    not_false_eq_true, List.nodup_nil, and_true] at fresh ⊢
  repeat' apply And.intro
  all_goals omega

end PASoundness.PAtoCompactLocalPairFresh

#print axioms PASoundness.PAtoCompactLocalPairFresh.pair_fresh_allocation
