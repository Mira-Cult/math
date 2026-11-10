import PASoundness.PAtoCompactCandidateSuccessor
import PASoundness.PAtoCompactCandidateAlpha

/-! K successor preservation for the exact shared-binder candidate shape in
PAtoCompactEmptyDomain. Input/output names differ only by the displayed
object, member-binder, subset-binder and nonempty-binder names. This does not
yet prove uniqueness, an equality quotient, induction or a PA interpretation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateExact
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactTransitiveDomain PASoundness.PAtoCompactPredecessor
open PASoundness.PAtoCompactLeastCounterexample PASoundness.PAtoCompactCandidateSuccessor
open PASoundness.PAtoCompactCandidateAlpha

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Exact syntactic candidate used in the zero-witness construction. -/
def candidateCode (x b p q a k l m g : Nat) : Nat :=
  both (oneLevelTransitiveCode x b p q)
    (both (greatestSubsetsCode x a k m g) (leastSubsetsCode x a k l m g))

/-- Any explicit successor of a candidate satisfies the same candidate
shape. Capture-safe alpha conversions align the shared test names; the output
member, subset and nonempty binders are freshly chosen. -/
def candidate_exact_successor (x y w b p q d s t a k m g u l r z v j : Nat)
    (fresh : [x,y,w,b,p,q,d,s,t,a,k,m,g,u,l,r,z,v,j].Nodup) :
    KDerivation (imp (candidateCode x b p q a k l m g) (imp (successorCode x y w)
      (candidateCode y d p q u k v m g))) := by
  have hinput : [x,a,k,l,m,g,r].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    tauto
  have houtput : [y,u,k,v,m,z,g].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    tauto
  have htrans : [y,s,t,p,q].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    tauto
  let D := candidateCode x b p q a k l m g
  let S := successorCode x y w
  let Γ := [S,D]
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have ht : Context Γ (oneLevelTransitiveCode x b p q) := Context.conjunctionLeft hd
  have he := Context.conjunctionRight hd
  have hg : Context Γ (greatestSubsetsCode x a k m g) := Context.conjunctionLeft he
  have hl : Context Γ (leastSubsetsCode x a k l m g) := Context.conjunctionRight he
  have hl' : Context Γ (leastSubsetsCode x a k l m r) :=
    .mp hl (.closed (least_subsets_rename x a k l m g r hinput))
  have hmid : Context Γ (both (oneLevelTransitiveCode x b p q)
      (both (greatestSubsetsCode x a k m g) (leastSubsetsCode x a k l m r))) :=
    Context.conjunctionIntro ht (Context.conjunctionIntro hg hl')
  have hout : Context Γ (both (both (transitiveCode y s t) (membersTransitiveCode y d p q))
      (both (greatestSubsetsCode y u k m g) (leastSubsetsCode y u k v m z))) :=
    .mp hs (.mp hmid (.closed (candidate_successor x y w b p q d s t a k m g u l r z v j fresh)))
  have ho := Context.conjunctionLeft hout
  have he' := Context.conjunctionRight hout
  have htnew : Context Γ (transitiveCode y p q) :=
    .mp (Context.conjunctionLeft ho) (.closed (transitive_rename y s t p q htrans))
  have hmnew : Context Γ (membersTransitiveCode y d p q) := Context.conjunctionRight ho
  have hgnew : Context Γ (greatestSubsetsCode y u k m g) := Context.conjunctionLeft he'
  have hlnew : Context Γ (leastSubsetsCode y u k v m g) :=
    .mp (Context.conjunctionRight he') (.closed (least_subsets_rename y u k v m z g houtput))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact Context.conjunctionIntro (Context.conjunctionIntro htnew hmnew)
    (Context.conjunctionIntro hgnew hlnew)

theorem candidate_exact_successor_certificate (x y w b p q d s t a k m g u l r z v j : Nat)
    (fresh : [x,y,w,b,p,q,d,s,t,a,k,m,g,u,l,r,z,v,j].Nodup) :
    theoremCode (certificate (candidate_exact_successor x y w b p q d s t a k m g u l r z v j fresh)) =
      imp (candidateCode x b p q a k l m g) (imp (successorCode x y w)
        (candidateCode y d p q u k v m g)) :=
  certificate_correct (candidate_exact_successor x y w b p q d s t a k m g u l r z v j fresh)

end PASoundness.PAtoCompactCandidateExact

#print axioms PASoundness.PAtoCompactCandidateExact.candidate_exact_successor
#print axioms PASoundness.PAtoCompactCandidateExact.candidate_exact_successor_certificate
