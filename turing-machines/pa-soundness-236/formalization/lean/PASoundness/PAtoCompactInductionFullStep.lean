import PASoundness.PAtoCompactPAInductionStepEngine
import PASoundness.PAtoCompactInductionPredicateAlignment
import PASoundness.PAtoCompactCandidateDomainAlphaIndependent
import PASoundness.PAtoCompactInductionFullSuccessorAlignment

/-! The PA induction step for an arbitrary PA formula. All pointwise
alignments are constructed without supplied K proof data, under the explicit
naming and allocation bounds. Matching the induction engine requires
specializing k=t and its separate freshness/selector obligations remain open.
This does not establish a PA induction axiom or the full PA-to-K bridge. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactInductionFullStep
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactUniformStep
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedAllElim PASoundness.PAtoCompactPAInductionPointwise
open PASoundness.PAtoCompactPAInductionStepEngine PASoundness.PAtoCompactInductionPredicateAlignment
open PASoundness.PAtoCompactCandidateDomainAlphaIndependent
open PASoundness.PAtoCompactInductionFullSuccessorAlignment
open PASoundness.PAtoCompactDirectGeneralization PASoundness.PAtoCompactGuardedGeneralizationAlignment
open PASoundness.PAtoCompactQuantifiedRefutation

/-- For the actual opened PA predicate, construct the step without supplied
K proof data. Name conditions and graph-allocation bounds remain explicit. -/
noncomputable def full_pa_step
    (φ : Peano.Formula) (x t : Nat)
    (Y y z w b p q v a k l h g r s d e i u j n c o graphBase : Nat)
    (htop : topName x φ < t) (hy : y < t) (hzt : z < t)
    (hyGraph : y < graphBase) (hzGraph : z < graphBase)
    (freshMember : [Y,y,b,p,q,v,a,k,l,h,g,r,s].Nodup)
    (freshSucc : [y,z,w,v,p,q,d,e,i,r,k,h,g,u,l,j,n,c,o].Nodup)
    (freshCy : [Y,b,p,q,a,k,l,h,g,y].Nodup)
    (freshCz : [Y,b,p,q,a,k,l,h,g,z].Nodup)
    (freshG : [Y,a,k,z,g,h].Nodup)
    (freshL : [Y,a,k,l,z,g,h].Nodup)
    (freshY : Y ∉ (Peano.inductionAxiom φ x).freeVarFinset)
    (freshy : y ∉ (Peano.inductionAxiom φ x).freeVarFinset)
    (freshz : z ∉ (Peano.inductionAxiom φ x).freeVarFinset)
 :
    KDerivation (imp (pointGuard φ x)
      (imp (code (FOL.allAt x (PAtoCompactPAInductionPointwise.paStep φ x)))
        (allCode Y (imp (candidateCode Y b p q a k l z g)
          (allStepsCode Y t y z w p q (scopeAt φ x t)))))) :=
  by
    have hnames : [y,v,p,q,r,k,l,h,g].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
        List.nodup_nil] at freshMember ⊢
      aesop
    have hbound : y < (instanceBinder (PAtoCompactPAInductionPointwise.paStep φ x) x y + 1) + 32 := by
      unfold instanceBinder
      omega
    have hdom := candidate_to_domain y v p q r k l h g
      (instanceBinder (PAtoCompactPAInductionPointwise.paStep φ x) x y + 1) hnames hbound
    have hwy : w ≠ y := by intro h'; subst w; simp at freshSucc
    have hwz : w ≠ z := by intro h'; subst w; simp at freshSucc
    let aux := z+y+d+p+q+v+u+k+c+h+g+r+1
    have hbase : [z,y,d,p,q,v,u,k,c,h,g,r].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
        List.nodup_nil] at freshSucc ⊢
      aesop
    have hsep : ∀ a ∈ [z,y,d,p,q,v,u,k,c,h,g,r], a ≠ aux := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        dsimp [aux] <;> omega
    have hcat : ([z,y,d,p,q,v,u,k,c,h,g,r] ++ [aux]).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨hbase, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      subst b
      exact hsep a ha
    have haux : [z,y,d,p,q,v,u,k,c,h,g,r,aux].Nodup := by simpa using hcat
    have hsuccessor := full_successor_alignment φ x t Y y z w p q d u k c h g v r aux graphBase
      htop hzt hyGraph hzGraph hwy hwz haux
    exact pa_step_engine φ x t (scopeAt φ x t) Y y z w b p q v a k l h g r s d e i u j n c o
      freshMember freshSucc freshCy freshCz freshG freshL freshY freshy freshz hdom
      (named_predicate_under φ x t y (pointGuard φ x) (candidateCode y v p q r k l h g) htop hy)
      hsuccessor

theorem full_pa_step_certificate
    (φ : Peano.Formula) (x t : Nat)
    (Y y z w b p q v a k l h g r s d e i u j n c o graphBase : Nat)
    (htop : topName x φ < t) (hy : y < t) (hzt : z < t)
    (hyGraph : y < graphBase) (hzGraph : z < graphBase)
    (freshMember : [Y,y,b,p,q,v,a,k,l,h,g,r,s].Nodup)
    (freshSucc : [y,z,w,v,p,q,d,e,i,r,k,h,g,u,l,j,n,c,o].Nodup)
    (freshCy : [Y,b,p,q,a,k,l,h,g,y].Nodup)
    (freshCz : [Y,b,p,q,a,k,l,h,g,z].Nodup)
    (freshG : [Y,a,k,z,g,h].Nodup)
    (freshL : [Y,a,k,l,z,g,h].Nodup)
    (freshY : Y ∉ (Peano.inductionAxiom φ x).freeVarFinset)
    (freshy : y ∉ (Peano.inductionAxiom φ x).freeVarFinset)
    (freshz : z ∉ (Peano.inductionAxiom φ x).freeVarFinset)
 :
    theoremCode (certificate (full_pa_step φ x t Y y z w b p q v a k l h g r s d e i u j n c o graphBase
      htop hy hzt hyGraph hzGraph freshMember freshSucc freshCy freshCz freshG freshL freshY freshy freshz)) =
      imp (pointGuard φ x)
        (imp (code (FOL.allAt x (PAtoCompactPAInductionPointwise.paStep φ x)))
          (allCode Y (imp (candidateCode Y b p q a k l z g)
            (allStepsCode Y t y z w p q (scopeAt φ x t))))) :=
  certificate_correct _
end PASoundness.PAtoCompactInductionFullStep

#print axioms PASoundness.PAtoCompactInductionFullStep.full_pa_step
#print axioms PASoundness.PAtoCompactInductionFullStep.full_pa_step_certificate
