import PASoundness.PAtoCompactCandidateExact
import PASoundness.PAtoCompactCandidateAlphaOuter
import PASoundness.PAtoCompactCandidateAlphaLeast
import PASoundness.PAtoCompactCandidateAlpha
import PASoundness.PAtoCompactGreatestInnerAlpha
import PASoundness.PAtoCompactGreatestWitnessAlpha
import PASoundness.PAtoCompactCandidateAlphaLeastWitness
import PASoundness.PAtoCompactCandidateAlphaSubsetTest

/-! Literal K transports for one candidate binder field at a time. Each
conversion has explicit syntactic freshness hypotheses; no extensionality,
semantic soundness, equality quotient, or PA proof interpretation is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateFieldTransport
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactTransitiveDomain
open PASoundness.PAtoCompactPredecessor PASoundness.PAtoCompactLeastCounterexample
open PASoundness.PAtoCompactCandidateAlphaOuter PASoundness.PAtoCompactCandidateAlphaLeast
open PASoundness.PAtoCompactCandidateAlpha PASoundness.PAtoCompactGreatestInnerAlpha
open PASoundness.PAtoCompactGreatestWitnessAlpha PASoundness.PAtoCompactCandidateAlphaLeastWitness
open PASoundness.PAtoCompactCandidateAlphaSubsetTest

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Combine three supplied literal K transports without changing their
antecedents or introducing a semantic premise. -/
def candidate_map (A B C A' B' C' : Nat)
    (hA : KDerivation (imp A A')) (hB : KDerivation (imp B B'))
    (hC : KDerivation (imp C C')) :
    KDerivation (imp (both A (both B C)) (both A' (both B' C'))) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [both A (both B C)]
  have h : Context Γ (both A (both B C)) := Context.head [] _
  have h1 : Context Γ A' := .mp (Context.conjunctionLeft h) (.closed hA)
  have h2 : Context Γ B' := .mp (Context.conjunctionLeft (Context.conjunctionRight h)) (.closed hB)
  have h3 : Context Γ C' := .mp (Context.conjunctionRight (Context.conjunctionRight h)) (.closed hC)
  exact Context.conjunctionIntro h1 (Context.conjunctionIntro h2 h3)

/-- Rename the member-transitivity binder. -/
def member_field (x b p q a k l m g n : Nat) (fresh : [x,b,p,q,n].Nodup) :
    KDerivation (imp (candidateCode x b p q a k l m g) (candidateCode x n p q a k l m g)) := by
  have hlevel : KDerivation (imp (oneLevelTransitiveCode x b p q) (oneLevelTransitiveCode x n p q)) := by
    apply Context.closeEmpty
    apply Context.deduction
    have h := Context.head [] (oneLevelTransitiveCode x b p q)
    exact Context.conjunctionIntro (Context.conjunctionLeft h)
      (.mp (Context.conjunctionRight h) (.closed (members_transitive_rename x b p q n fresh)))
  exact candidate_map _ _ _ _ _ _ hlevel (CompactHilbertBasis.identity _) (CompactHilbertBasis.identity _)

/-- Rename the shared outer subset binder in both extremum conditions. -/
def subset_field (x b p q a k l m g n : Nat)
    (freshG : [x,a,k,m,g,n].Nodup) (freshL : [x,a,k,l,m,g,n].Nodup) :
    KDerivation (imp (candidateCode x b p q a k l m g) (candidateCode x b p q n k l m g)) :=
  candidate_map _ _ _ _ _ _ (CompactHilbertBasis.identity _)
    (greatest_subsets_rename_outer x a k m g n freshG)
    (least_subsets_outer_rename x a k l m g n freshL)

/-- Rename the nonemptiness witness binder in the least-subset condition. -/
def nonempty_field (x b p q a k l m g n : Nat) (fresh : [x,a,k,l,m,g,n].Nodup) :
    KDerivation (imp (candidateCode x b p q a k l m g) (candidateCode x b p q a k n m g)) :=
  candidate_map _ _ _ _ _ _ (CompactHilbertBasis.identity _) (CompactHilbertBasis.identity _)
    (least_subsets_nonempty_rename x a k l m g n fresh)

/-- Rename the membership-order test in both extremum conditions. -/
def order_field (x b p q a k l m g n : Nat)
    (freshG : [x,a,k,m,g,n].Nodup) (freshL : [x,a,k,l,m,g,n].Nodup) :
    KDerivation (imp (candidateCode x b p q a k l m g) (candidateCode x b p q a k l m n)) :=
  candidate_map _ _ _ _ _ _ (CompactHilbertBasis.identity _)
    (greatest_subsets_rename_order x a k m g n freshG) (least_subsets_rename x a k l m g n freshL)

/-- Rename the existential least/greatest witness binder. -/
def witness_field (x b p q a k l m g n : Nat)
    (freshG : [x,a,k,m,g,n].Nodup) (freshL : [x,a,k,l,m,g,n].Nodup) :
    KDerivation (imp (candidateCode x b p q a k l m g) (candidateCode x b p q a k l n g)) :=
  candidate_map _ _ _ _ _ _ (CompactHilbertBasis.identity _)
    (greatest_witness_rename x a k m g n freshG) (least_witness_rename x a k l m g n freshL)

/-- Rename the subset-membership test in both extremum conditions. -/
def subset_test_field (x b p q a k l m g n : Nat)
    (freshG : [x,a,k,m,g,n].Nodup) (freshL : [x,a,k,l,m,g,n].Nodup) :
    KDerivation (imp (candidateCode x b p q a k l m g) (candidateCode x b p q a n l m g)) :=
  candidate_map _ _ _ _ _ _ (CompactHilbertBasis.identity _)
    (greatest_subset_test_rename x a k m g n freshG) (least_subset_test_rename x a k l m g n freshL)

end PASoundness.PAtoCompactCandidateFieldTransport

#print axioms PASoundness.PAtoCompactCandidateFieldTransport.member_field
#print axioms PASoundness.PAtoCompactCandidateFieldTransport.subset_field
#print axioms PASoundness.PAtoCompactCandidateFieldTransport.nonempty_field
#print axioms PASoundness.PAtoCompactCandidateFieldTransport.order_field
#print axioms PASoundness.PAtoCompactCandidateFieldTransport.witness_field
#print axioms PASoundness.PAtoCompactCandidateFieldTransport.subset_test_field
