import PASoundness.PAtoCompactInductionSuccGraph
import PASoundness.PAtoCompactCandidateMemberClosure
import PASoundness.PAtoCompactCandidateDomainAlphaIndependent
import PASoundness.PAtoCompactUniformStep

/-! The exact successor-term graph follows from the output being a candidate
and the predecessor core: successor membership makes the input a member of
the candidate output, and candidate inheritance supplies its domain guard.
All freshness and allocation bounds are explicit. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPAInductionOutputGraph
open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidateMemberClosure
open PASoundness.PAtoCompactCandidateDomainAlphaIndependent PASoundness.PAtoCompactUniformStep
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactInductionSuccGraph
open PASoundness.PAtoCompactTermTranslation

/-- From candidate output z and the raw successor in predecessorCore, construct
the literal term graph for S(y) at z, without assuming candidate(Y). -/
def output_candidate_term_graph
    (base Y y z w p q d u k c h g v r s : Nat)
    (hy : y < base) (hz : z < base) (hwy : w ≠ y) (hwz : w ≠ z)
    (fresh : [z,y,d,p,q,v,u,k,c,h,g,r,s].Nodup) :
    KDerivation (imp (candidateCode z d p q u k c h g)
      (imp (predecessorCore Y y z w p q)
        (termGraph (fun n : Nat => n) (Peano.succ (.var y)) z base).encode)) := by
  have fz : [z,d,p,q,u,k,c,h,g].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
      List.nodup_nil] at fresh ⊢
    aesop
  have fy : [y,v,p,q,r,k,c,h,g].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
      List.nodup_nil] at fresh ⊢
    aesop
  let C := candidateCode z d p q u k c h g
  let P := predecessorCore Y y z w p q
  let S := successorCode y z w
  let D := candidateCode y v p q r k c h g
  let Γ := [P,C]
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hs : Context Γ S := Context.conjunctionLeft (Context.conjunctionRight hp)
  have hm : Context Γ (member z y) := .mp hs (.closed (successor_contains_input y z w hwy hwz))
  have hd : Context Γ D := .mp hm (.mp hc (.closed (candidate_member z y d p q v u k c h g r s fresh)))
  have hdy : Context Γ (domainAt base y).encode :=
    .mp hd (.closed (candidate_to_domain y v p q r k c h g base fy (by omega)))
  have hdz : Context Γ (domainAt base z).encode :=
    .mp hc (.closed (candidate_to_domain z d p q u k c h g base fz (by omega)))
  have hgraph : Context Γ (termGraph (fun n : Nat => n) (Peano.succ (.var y)) z base).encode :=
    .mp hs (.mp hdz (.mp hdy (.closed (successor_term_graph base y z w hy hz hwy hwz))))
  exact Context.closeEmpty (Context.deduction (Context.deduction hgraph))

theorem output_candidate_term_graph_certificate
    (base Y y z w p q d u k c h g v r s : Nat)
    (hy : y < base) (hz : z < base) (hwy : w ≠ y) (hwz : w ≠ z)
    (fresh : [z,y,d,p,q,v,u,k,c,h,g,r,s].Nodup) :
    theoremCode (certificate (output_candidate_term_graph base Y y z w p q d u k c h g v r s
      hy hz hwy hwz fresh)) =
      imp (candidateCode z d p q u k c h g) (imp (predecessorCore Y y z w p q)
        (termGraph (fun n : Nat => n) (Peano.succ (.var y)) z base).encode) :=
  certificate_correct _
end PASoundness.PAtoCompactPAInductionOutputGraph

#print axioms PASoundness.PAtoCompactPAInductionOutputGraph.output_candidate_term_graph
#print axioms PASoundness.PAtoCompactPAInductionOutputGraph.output_candidate_term_graph_certificate
