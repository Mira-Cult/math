import PASoundness.PAtoCompactLeastSuccessorEmptyExists
import PASoundness.PAtoCompactLeastSuccessorNonempty

/-! Least-subset successor step for one explicitly represented intersection.
The graph is still a hypothesis; this does not yet establish domain closure. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLeastSuccessorBranches
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPredecessor
open PASoundness.PAtoCompactLeastCounterexample PASoundness.PAtoCompactLeastSuccessorCase
open PASoundness.PAtoCompactLeastSuccessorEmptyExists PASoundness.PAtoCompactLeastSuccessorNonempty

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Both cases for the explicit intersection c, retaining one shared least
witness formula and all named hypotheses. -/
def least_of_intersection (x y w u k c q a z m r b v : Nat)
    (fresh : [x,y,w,u,k,c,q,a,z,m,r,b,v].Nodup) :
    KDerivation (imp (successorCode x y w) (imp (subsetCode u y k)
      (imp (intersectionGraph u x c q) (imp (leastSubsetsCode x b k a m r)
        (imp (nonemptyCode u v) (existsCode m (leastMemberCode u m z))))))) := by
  have hpos : [x,y,w,u,k,c,q,a,z,m,r,b].Nodup := by
    exact List.Nodup.sublist (List.sublist_append_left [x,y,w,u,k,c,q,a,z,m,r,b] [v]) fresh
  have hneg : [x,y,w,u,k,c,q,a,z,v,m].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    aesop
  let S := successorCode x y w
  let U := subsetCode u y k
  let I := intersectionGraph u x c q
  let L := leastSubsetsCode x b k a m r
  let N := nonemptyCode u v
  let E := nonemptyCode c a
  let H := existsCode m (leastMemberCode u m z)
  let Γ := [N,L,I,U,S]
  have hn : Context Γ N := .hypothesis (by simp [Γ])
  have hl : Context Γ L := .hypothesis (by simp [Γ])
  have hi : Context Γ I := .hypothesis (by simp [Γ])
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have he : KDerivation (either E (neg E)) := CompactHilbertBasis.identity (neg E)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.disjunctionElim (Context.closed he : Context Γ (either E (neg E)))
  · have hp : Context (E :: Γ) E := Context.head Γ E
    exact .mp hp (.mp (Context.under hl _) (.mp (Context.under hi _)
      (.mp (Context.under hu _) (.mp (Context.under hs _)
        (.closed (nonempty_intersection_has_least x y w u k c q a z m r b hpos))))))
  · have hp : Context (neg E :: Γ) (neg E) := Context.head Γ (neg E)
    exact .mp (Context.under hn _) (.mp hp (.mp (Context.under hi _)
      (.mp (Context.under hu _) (.mp (Context.under hs _)
        (.closed (empty_intersection_has_least x y w u k c q a z v m hneg))))))

theorem least_of_intersection_certificate (x y w u k c q a z m r b v : Nat)
    (fresh : [x,y,w,u,k,c,q,a,z,m,r,b,v].Nodup) :
    theoremCode (certificate (least_of_intersection x y w u k c q a z m r b v fresh)) =
      imp (successorCode x y w) (imp (subsetCode u y k)
        (imp (intersectionGraph u x c q) (imp (leastSubsetsCode x b k a m r)
          (imp (nonemptyCode u v) (existsCode m (leastMemberCode u m z)))))) :=
  certificate_correct (least_of_intersection x y w u k c q a z m r b v fresh)

end PASoundness.PAtoCompactLeastSuccessorBranches

#print axioms PASoundness.PAtoCompactLeastSuccessorBranches.least_of_intersection
#print axioms PASoundness.PAtoCompactLeastSuccessorBranches.least_of_intersection_certificate
