import PASoundness.PAtoCompactGreatestDownward
import PASoundness.PAtoCompactLeastCounterexample

/-! Capture-safe replacement of the subset-test binder in the K candidate's
greatest- and least-subsets clauses. These are finite syntactic proof-data
constructions, with no semantic soundness or arithmetic interpretation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateAlphaSubsetTest
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactPredecessor PASoundness.PAtoCompactGreatestDownward
open PASoundness.PAtoCompactLeastCounterexample
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A reverse subset conversion transports an arbitrary consequent across
the subset antecedent. All names are explicit and pairwise fresh. -/
def subset_antecedent_rename (x u k z A : Nat) (fresh : [x,u,k,z].Nodup) :
    KDerivation (imp (imp (subsetCode u x k) A) (imp (subsetCode u x z) A)) := by
  have hzk : z ≠ k := by intro h; subst z; simp at fresh
  have hzu : z ≠ u := by intro h; subst z; simp at fresh
  have hzx : z ≠ x := by intro h; subst z; simp at fresh
  have hku : k ≠ u := by intro h; subst k; simp at fresh
  have hkx : k ≠ x := by intro h; subst k; simp at fresh
  have hr := subset_rename u x z k hzk hzu hzx hku hkx
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [subsetCode u x z, imp (subsetCode u x k) A]
  have hz : Context Γ (subsetCode u x z) := Context.head _ _
  have hi : Context Γ (imp (subsetCode u x k) A) := .hypothesis (by simp [Γ])
  exact .mp (.mp hz (.closed hr)) hi

/-- Rename the internal subset-test binder in the greatest-subsets clause. -/
def greatest_subset_test_rename (x u k m t z : Nat) (fresh : [x,u,k,m,t,z].Nodup) :
    KDerivation (imp (greatestSubsetsCode x u k m t) (greatestSubsetsCode x u z m t)) := by
  have hn : [x,u,k,z].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    tauto
  exact allCongr u (subset_antecedent_rename x u k z
    (imp (nonemptyCode u m) (hasGreatestCode u m t)) hn)

/-- Rename the internal subset-test binder in the least-subsets clause. -/
def least_subset_test_rename (x u k a m t z : Nat) (fresh : [x,u,k,a,m,t,z].Nodup) :
    KDerivation (imp (leastSubsetsCode x u k a m t) (leastSubsetsCode x u z a m t)) := by
  have hn : [x,u,k,z].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    tauto
  exact allCongr u (subset_antecedent_rename x u k z
    (imp (nonemptyCode u a) (existsCode m (leastMemberCode u m t))) hn)

theorem greatest_subset_test_rename_certificate (x u k m t z : Nat)
    (fresh : [x,u,k,m,t,z].Nodup) :
    theoremCode (certificate (greatest_subset_test_rename x u k m t z fresh)) =
      imp (greatestSubsetsCode x u k m t) (greatestSubsetsCode x u z m t) :=
  certificate_correct (greatest_subset_test_rename x u k m t z fresh)

theorem least_subset_test_rename_certificate (x u k a m t z : Nat)
    (fresh : [x,u,k,a,m,t,z].Nodup) :
    theoremCode (certificate (least_subset_test_rename x u k a m t z fresh)) =
      imp (leastSubsetsCode x u k a m t) (leastSubsetsCode x u z a m t) :=
  certificate_correct (least_subset_test_rename x u k a m t z fresh)

end PASoundness.PAtoCompactCandidateAlphaSubsetTest

#print axioms PASoundness.PAtoCompactCandidateAlphaSubsetTest.greatest_subset_test_rename
#print axioms PASoundness.PAtoCompactCandidateAlphaSubsetTest.least_subset_test_rename
#print axioms PASoundness.PAtoCompactCandidateAlphaSubsetTest.greatest_subset_test_rename_certificate
#print axioms PASoundness.PAtoCompactCandidateAlphaSubsetTest.least_subset_test_rename_certificate
