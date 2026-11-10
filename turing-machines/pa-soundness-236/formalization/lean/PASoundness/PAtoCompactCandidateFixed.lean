import PASoundness.PAtoCompactCandidateWitness
import PASoundness.PAtoCompactCandidateAlphaOuter
import PASoundness.PAtoCompactCandidateAlphaLeast

/-! Capture-safe normalization and successor witness for the exact candidate
with fixed displayed binder names. This is not an arithmetic interpretation,
quotient, or induction proof; code 1 is literal self-membership. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateFixed
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactTransitiveDomain PASoundness.PAtoCompactPredecessor
open PASoundness.PAtoCompactLeastCounterexample PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidateWitness
open PASoundness.PAtoCompactCandidateAlphaOuter PASoundness.PAtoCompactCandidateAlphaLeast

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Normalize the output member, subset and nonemptiness binders to the
specified fixed candidate names by actual K alpha-conversion derivations. -/
def candidate_normalize (y d b p q u a k v l m g : Nat)
    (fresh : [y,d,b,p,q,u,a,k,v,l,m,g].Nodup) :
    KDerivation (imp (candidateCode y d p q u k v m g)
      (candidateCode y b p q a k l m g)) := by
  have hm : [y,d,p,q,b].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    tauto
  have hg : [y,u,k,m,g,a].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    tauto
  have hl : [y,u,k,v,m,g,a].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    tauto
  have hl' : [y,a,k,v,m,g,l].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    tauto
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [candidateCode y d p q u k v m g]
  have hd : Context Γ (candidateCode y d p q u k v m g) := Context.head [] _
  have ht := Context.conjunctionLeft (Context.conjunctionLeft hd)
  have hmem := Context.conjunctionRight (Context.conjunctionLeft hd)
  have hg0 := Context.conjunctionLeft (Context.conjunctionRight hd)
  have hl0 := Context.conjunctionRight (Context.conjunctionRight hd)
  have hmem' : Context Γ (membersTransitiveCode y b p q) :=
    .mp hmem (.closed (members_transitive_rename y d p q b hm))
  have hg' : Context Γ (greatestSubsetsCode y a k m g) :=
    .mp hg0 (.closed (greatest_subsets_rename_outer y u k m g a hg))
  have hl1 : Context Γ (leastSubsetsCode y a k v m g) :=
    .mp hl0 (.closed (least_subsets_outer_rename y u k v m g a hl))
  have hl2 : Context Γ (leastSubsetsCode y a k l m g) :=
    .mp hl1 (.closed (least_subsets_nonempty_rename y a k v m g l hl'))
  exact Context.conjunctionIntro (Context.conjunctionIntro ht hmem')
    (Context.conjunctionIntro hg' hl2)

/-- An explicit successor preserves the very same candidate formula with the
object variable changed capture-safely from x to y. -/
def fixed_candidate_successor (x y w b p q d s t a k m g u l r z v j : Nat)
    (fresh : [x,y,w,b,p,q,d,s,t,a,k,m,g,u,l,r,z,v,j].Nodup) :
    KDerivation (imp (candidateCode x b p q a k l m g) (imp (successorCode x y w)
      (candidateCode y b p q a k l m g))) := by
  have hn : [y,d,b,p,q,u,a,k,v,l,m,g].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    tauto
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [successorCode x y w, candidateCode x b p q a k l m g]
  have hs : Context Γ (successorCode x y w) := .hypothesis (by simp [Γ])
  have hd : Context Γ (candidateCode x b p q a k l m g) := .hypothesis (by simp [Γ])
  have ht : Context Γ (candidateCode y d p q u k v m g) := .mp hs (.mp hd
    (.closed (candidate_exact_successor x y w b p q d s t a k m g u l r z v j fresh)))
  exact .mp ht (.closed (candidate_normalize y d b p q u a k v l m g hn))

/-- K constructs a successor in the fixed displayed candidate predicate. The
selector-code side conditions and freshness of syntactic names are explicit. -/
def fixed_candidate_successor_exists (x y w b p q d s t a k m g u l r z v j point : Nat)
    (fresh : [x,y,w,b,p,q,d,s,t,a,k,m,g,u,l,r,z,v,j,point].Nodup)
    (hwc : w ≠ adjunctionPredicate x point)
    (hyc : y ≠ adjunctionPredicate x point) :
    KDerivation (imp (candidateCode x b p q a k l m g)
      (existsCode y (both (successorCode x y w) (candidateCode y b p q a k l m g)))) := by
  have hn : [y,d,b,p,q,u,a,k,v,l,m,g].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    tauto
  have hmap : KDerivation (imp
      (both (successorCode x y w) (candidateCode y d p q u k v m g))
      (both (successorCode x y w) (candidateCode y b p q a k l m g))) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [both (successorCode x y w) (candidateCode y d p q u k v m g)]
    have h := Context.head [] (both (successorCode x y w) (candidateCode y d p q u k v m g))
    exact Context.conjunctionIntro (Context.conjunctionLeft h)
      (.mp (Context.conjunctionRight h) (.closed (candidate_normalize y d b p q u a k v l m g hn)))
  exact compose (candidate_successor_exists x y w b p q d s t a k m g u l r z v j point fresh hwc hyc)
    (existsCongr y hmap)

theorem fixed_candidate_successor_exists_certificate (x y w b p q d s t a k m g u l r z v j point : Nat)
    (fresh : [x,y,w,b,p,q,d,s,t,a,k,m,g,u,l,r,z,v,j,point].Nodup)
    (hwc : w ≠ adjunctionPredicate x point)
    (hyc : y ≠ adjunctionPredicate x point) :
    theoremCode (certificate (fixed_candidate_successor_exists x y w b p q d s t a k m g u l r z v j point fresh hwc hyc)) =
      imp (candidateCode x b p q a k l m g)
        (existsCode y (both (successorCode x y w) (candidateCode y b p q a k l m g))) :=
  certificate_correct (fixed_candidate_successor_exists x y w b p q d s t a k m g u l r z v j point fresh hwc hyc)

end PASoundness.PAtoCompactCandidateFixed

#print axioms PASoundness.PAtoCompactCandidateFixed.fixed_candidate_successor
#print axioms PASoundness.PAtoCompactCandidateFixed.fixed_candidate_successor_exists
#print axioms PASoundness.PAtoCompactCandidateFixed.fixed_candidate_successor_exists_certificate
