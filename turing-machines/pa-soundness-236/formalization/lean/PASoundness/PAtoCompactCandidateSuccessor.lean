import PASoundness.PAtoCompactTransitiveDomain
import PASoundness.PAtoCompactGreatestSuccessorClosed
import PASoundness.PAtoCompactLeastSuccessorFresh

/-! Successor preservation for the transitivity-and-extrema candidate
fragment. Output formulas deliberately retain their displayed, potentially
different alpha-bound names. This is not a fixed-syntax domain theorem, an
equality quotient, arithmetic induction, or a PA proof translation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateSuccessor
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactTransitiveDomain PASoundness.PAtoCompactPredecessor
open PASoundness.PAtoCompactLeastCounterexample PASoundness.PAtoCompactGreatestSuccessorClosed
open PASoundness.PAtoCompactLeastSuccessorFresh

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Simultaneous preservation of the four explicit properties: transitivity,
transitivity of each member, and least/greatest represented subsets. Binder
names in the conclusion are displayed independently from their input names. -/
def candidate_successor (x y w b p q d s t a k m g u l r z v j : Nat)
    (fresh : [x,y,w,b,p,q,d,s,t,a,k,m,g,u,l,r,z,v,j].Nodup) :
    KDerivation (imp
      (both (oneLevelTransitiveCode x b p q)
        (both (greatestSubsetsCode x a k m g) (leastSubsetsCode x a k l m r)))
      (imp (successorCode x y w)
        (both (both (transitiveCode y s t) (membersTransitiveCode y d p q))
          (both (greatestSubsetsCode y u k m g) (leastSubsetsCode y u k v m z))))) := by
  have htrans : [x,y,w,b,p,q,d,s,t].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    tauto
  have hgreat : [x,y,w,a,k,m,g,u,j].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    tauto
  have hleast : [x,y,w,u,k,l,z,m,r,a,v].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    tauto
  let D := both (oneLevelTransitiveCode x b p q)
    (both (greatestSubsetsCode x a k m g) (leastSubsetsCode x a k l m r))
  let S := successorCode x y w
  let Γ := [S,D]
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have ht : Context Γ (oneLevelTransitiveCode x b p q) := Context.conjunctionLeft hd
  have he := Context.conjunctionRight hd
  have hg : Context Γ (greatestSubsetsCode x a k m g) := Context.conjunctionLeft he
  have hl : Context Γ (leastSubsetsCode x a k l m r) := Context.conjunctionRight he
  have ht' : Context Γ (both (transitiveCode y s t) (membersTransitiveCode y d p q)) :=
    .mp hs (.mp ht (.closed (successor_one_level_transitive x y w b p q d s t htrans)))
  have hg' : Context Γ (greatestSubsetsCode y u k m g) :=
    .mp hs (.mp hg (.closed (successor_greatest_subsets x y w a k m g u j hgreat)))
  have hl' : Context Γ (leastSubsetsCode y u k v m z) :=
    .mp hs (.mp hl (.closed (successor_least_subsets_fresh x y w u k l z m r a v hleast)))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact Context.conjunctionIntro ht' (Context.conjunctionIntro hg' hl')

theorem candidate_successor_certificate (x y w b p q d s t a k m g u l r z v j : Nat)
    (fresh : [x,y,w,b,p,q,d,s,t,a,k,m,g,u,l,r,z,v,j].Nodup) :
    theoremCode (certificate (candidate_successor x y w b p q d s t a k m g u l r z v j fresh)) =
      imp (both (oneLevelTransitiveCode x b p q)
        (both (greatestSubsetsCode x a k m g) (leastSubsetsCode x a k l m r)))
      (imp (successorCode x y w)
        (both (both (transitiveCode y s t) (membersTransitiveCode y d p q))
          (both (greatestSubsetsCode y u k m g) (leastSubsetsCode y u k v m z)))) :=
  certificate_correct (candidate_successor x y w b p q d s t a k m g u l r z v j fresh)

end PASoundness.PAtoCompactCandidateSuccessor

#print axioms PASoundness.PAtoCompactCandidateSuccessor.candidate_successor
#print axioms PASoundness.PAtoCompactCandidateSuccessor.candidate_successor_certificate
