import PASoundness.PAtoCompactFullInductionPointComposition
import PASoundness.PAtoCompactInductionConclusionAligned

/-! A conditional K proof of the full PA induction
axiom, assembled from its translated base and step, a supplied actual finite K
candidate-induction engine proof, and the checked universal conclusion
packaging. Constructing the supplied engine proof requires its separate
freshness and selector obligations; name allocation remains open. No full
PA-to-K compiler is established. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFullInductionConditional
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactUniformBase
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactGuardedAllElim PASoundness.PAtoCompactGuardedAllImp
open PASoundness.PAtoCompactGuardedAllImpAlignment PASoundness.PAtoCompactGuardedGeneralizationAlignment
open PASoundness.PAtoCompactDirectGeneralization
open PASoundness.PAtoCompactVacuousQuantifierFree PASoundness.PAtoCompactQuantifiedRefutation
open PASoundness.PAtoCompactFullInductionPointComposition PASoundness.PAtoCompactInductionConclusionAligned

/-- An actual engine proof is the only K proof-data input. All external
syntactic freshness and allocator requirements are displayed explicitly. -/
noncomputable def full_induction_of_engine
    (φ : Peano.Formula) (x m base point Y v w bD p q u l r : Nat)
    (va ha ra sa da ea ia ua ja na ca oa : Nat)
    (hm : m < base) (hvbase : v < base)
    (hv : v < instanceBinder φ x m)
    (freshMember : [Y,v,bD,p,q,va,u,instanceBinder φ x m,l,ha,r,ra,sa].Nodup)
    (freshSucc : [v,m,w,va,p,q,da,ea,ia,ra,instanceBinder φ x m,ha,r,ua,l,ja,na,ca,oa].Nodup)
    (freshCy : [Y,bD,p,q,u,instanceBinder φ x m,l,ha,r,v].Nodup)
    (freshCz : [Y,bD,p,q,u,instanceBinder φ x m,l,ha,r,m].Nodup)
    (freshG : [Y,u,instanceBinder φ x m,m,r,ha].Nodup)
    (freshL : [Y,u,instanceBinder φ x m,l,m,r,ha].Nodup)
    (freshY : Y ∉ (Peano.inductionAxiom φ x).freeVarFinset)
    (freshv : v ∉ (Peano.inductionAxiom φ x).freeVarFinset)
    (freshm : m ∉ (Peano.inductionAxiom φ x).freeVarFinset)
    (hpointGt : topName x φ < point)
    (hpointChild : point ∉ (originalChild φ x).names)
    (hpointFree : point ∉ (Peano.inductionAxiom φ x).freeVarFinset)
    (hpointLt : point < instanceBinder φ x m)
    (freshPoint : [point,bD,p,q,u,instanceBinder φ x m,l,m,r].Nodup)
    (engine : let t := instanceBinder φ x m
      let f := scopeAt φ x t
      KDerivation (imp (candidateCode point bD p q u t l m r)
        (imp (uniformBaseCode t m (base+3) f)
          (imp (allCode Y (imp (candidateCode Y bD p q u t l m r)
            (allStepsCode Y t v m w p q f)))
            (replace t point f).encode)))) : KDerivation (guardedCode (Peano.inductionAxiom φ x)) := by
  let t := instanceBinder φ x m
  have htop : topName x φ < t := by
    have hh := ceiling_top φ x
    dsimp [t, instanceBinder]
    omega
  have hp := full_point_of_engine φ x m base point Y v w bD p q u l r
    va ha ra sa da ea ia ua ja na ca oa hm hvbase hv
    freshMember freshSucc freshCy freshCz freshG freshL freshY freshv freshm engine
  exact close_from_candidate_pointwise φ x point bD p q u t l m r hpointGt hpointChild
    hpointFree htop hpointLt freshPoint hp

end PASoundness.PAtoCompactFullInductionConditional

#print axioms PASoundness.PAtoCompactFullInductionConditional.full_induction_of_engine
