import PASoundness.PAtoCompactEmptyExtrema
import PASoundness.PAtoCompactTransitiveDomain
import PASoundness.PAtoCompactZeroTransitive

/-! K construction of a zero witness in the displayed transitivity/extrema
fragment. The candidate does not give uniqueness, quotient equality, PA
operations, or induction; code 1 retains its literal self-membership meaning. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactEmptyDomain
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactZeroExistence
open PASoundness.PAtoCompactZeroTransitive PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactTransitiveDomain PASoundness.PAtoCompactPredecessor
open PASoundness.PAtoCompactLeastCounterexample PASoundness.PAtoCompactEmptyExtrema
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Every zero-graph object has the displayed transitive and transitive-member
fragment. All object and binder names are fresh. -/
def zero_one_level_transitive (x z b p q : Nat) (fresh : [x,z,b,p,q].Nodup) :
    KDerivation (imp (zeroCode x z) (oneLevelTransitiveCode x b p q)) := by
  have hzx : z ≠ x := by intro h; subst z; simp at fresh
  have hzp : z ≠ p := by intro h; subst z; simp at fresh
  have hzb : z ≠ b := by intro h; subst z; simp at fresh
  have hpx : p ≠ x := by intro h; subst p; simp at fresh
  have hqx : q ≠ x := by intro h; subst q; simp at fresh
  have hqz : q ≠ z := by intro h; subst q; simp at fresh
  have hpq : p ≠ q := by intro h; subst p; simp at fresh
  have hbx : b ≠ x := by intro h; subst b; simp at fresh
  let Z := zeroCode x z
  let Γ := [Z]
  have hz : Context Γ Z := Context.head [] Z
  have ht : Context Γ (transitiveCode x p q) :=
    .mp hz (.closed (zero_graph_implies_transitive x z p q hzx hzp hpx hqx hqz hpq))
  have hp : Context Γ (imp (member x b) (transitiveCode b p q)) := by
    apply Context.deduction
    have hm : Context (member x b :: Γ) (member x b) := Context.head Γ _
    have hno : Context (member x b :: Γ) (neg (member x b)) :=
      .mp (Context.under hz _) (.closed (zero_excludes x z b hzb hzx))
    exact Context.explode (transitiveCode b p q) (.mp hm hno)
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode b h)) := by
    intro h hh
    have he : h = Z := by simpa [Γ] using hh
    subst h
    exact zero_vacuity x z b hbx (Ne.symm hzb)
  have hm : Context Γ (membersTransitiveCode x b p q) := Context.generalize b hv hp
  apply Context.closeEmpty
  apply Context.deduction
  exact Context.conjunctionIntro ht hm

/-- K derives the entire displayed domain fragment from its zero graph. -/
def zero_candidate (x z b p q u k a m r : Nat)
    (fresh : [x,z,b,p,q,u,k,a,m,r].Nodup) :
    KDerivation (imp (zeroCode x z)
      (both (oneLevelTransitiveCode x b p q)
        (both (greatestSubsetsCode x u k m r) (leastSubsetsCode x u k a m r)))) := by
  have htransFresh : [x,z,b,p,q].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, not_false_eq_true] at fresh ⊢
    tauto
  have hextFresh : [x,z,u,k,a,m,r].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, not_false_eq_true] at fresh ⊢
    tauto
  apply Context.closeEmpty
  apply Context.deduction
  have hz : Context [zeroCode x z] (zeroCode x z) := Context.head [] _
  have ht : Context [zeroCode x z] (oneLevelTransitiveCode x b p q) :=
    .mp hz (.closed (zero_one_level_transitive x z b p q htransFresh))
  have he : Context [zeroCode x z]
      (both (leastSubsetsCode x u k a m r) (greatestSubsetsCode x u k m r)) :=
    .mp hz (.closed (zero_has_subset_extrema x z u k a m r hextFresh))
  exact Context.conjunctionIntro ht
    (Context.conjunctionIntro (Context.conjunctionRight he) (Context.conjunctionLeft he))

/-- An explicit zero-domain witness is derivable in K. -/
def candidate_zero_exists : KDerivation
    (existsCode 1 (both (zeroCode 1 2)
      (both (oneLevelTransitiveCode 1 3 4 5)
        (both (greatestSubsetsCode 1 6 7 9 10) (leastSubsetsCode 1 6 7 8 9 10))))) := by
  apply KDerivation.mp zero_graph_exists_closed
  apply existsCongr 1
  apply Context.closeEmpty
  apply Context.deduction
  have hz := Context.head [] (zeroCode 1 2)
  exact Context.conjunctionIntro hz (.mp hz (.closed
    (zero_candidate 1 2 3 4 5 6 7 8 9 10 (by decide))))

theorem candidate_zero_certificate :
    theoremCode (certificate candidate_zero_exists) =
      existsCode 1 (both (zeroCode 1 2)
        (both (oneLevelTransitiveCode 1 3 4 5)
          (both (greatestSubsetsCode 1 6 7 9 10) (leastSubsetsCode 1 6 7 8 9 10)))) :=
  certificate_correct candidate_zero_exists

end PASoundness.PAtoCompactEmptyDomain

#print axioms PASoundness.PAtoCompactEmptyDomain.zero_one_level_transitive
#print axioms PASoundness.PAtoCompactEmptyDomain.zero_candidate
#print axioms PASoundness.PAtoCompactEmptyDomain.candidate_zero_exists
#print axioms PASoundness.PAtoCompactEmptyDomain.candidate_zero_certificate
