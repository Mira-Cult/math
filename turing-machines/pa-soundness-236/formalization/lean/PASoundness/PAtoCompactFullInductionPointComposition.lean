import PASoundness.PAtoCompactInductionFullZeroBase
import PASoundness.PAtoCompactInductionFullStep
import PASoundness.PAtoCompactCandidateRestrictedInduction

/-! Exact finite-K composition of the checked PA base and step with a supplied
candidate-restricted induction engine instance. This leaves the engine's
freshness and selector obligations, source-to-point alignment, and universal
packaging explicit; it is not a PA induction axiom proof. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFullInductionPointComposition
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactUniformBase
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactGuardedAllElim PASoundness.PAtoCompactGuardedAllImp
open PASoundness.PAtoCompactGuardedGeneralizationAlignment PASoundness.PAtoCompactDirectGeneralization
open PASoundness.PAtoCompactPAInductionPointwise
open PASoundness.PAtoCompactVacuousQuantifierFree PASoundness.PAtoCompactInductionFullZeroBase
open PASoundness.PAtoCompactInductionFullStep PASoundness.PAtoCompactQuantifiedRefutation

/-- The output is a named point instance under the actual PA induction base,
step and parameter guard. The finite K engine proof is an explicit input, so
its selection, name and freshness requirements are not silently discharged. -/
noncomputable def full_point_of_engine
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
    (engine : let t := instanceBinder φ x m
      let f := scopeAt φ x t
      KDerivation (imp (candidateCode point bD p q u t l m r)
        (imp (uniformBaseCode t m (base+3) f)
          (imp (allCode Y (imp (candidateCode Y bD p q u t l m r)
            (allStepsCode Y t v m w p q f)))
            (replace t point f).encode)))) :
    let t := instanceBinder φ x m
    let f := scopeAt φ x t
    KDerivation (imp (pointGuard φ x)
      (imp (code (FOL.substAt φ x Peano.zero))
        (imp (code (FOL.allAt x (paStep φ x)))
          (imp (candidateCode point bD p q u t l m r)
            (replace t point f).encode)))) := by
  dsimp only at engine ⊢
  let t := instanceBinder φ x m
  let f := scopeAt φ x t
  have htop : topName x φ < t := by
    have hh := ceiling_top φ x
    dsimp [t, instanceBinder]
    omega
  have hmt : m < t := by dsimp [t, instanceBinder]; omega
  have hb := full_zero_uniform_base φ x m base hm freshm
  have hs := full_pa_step φ x t Y v m w bD p q va u t l ha r ra sa da ea ia ua ja na ca oa base
    htop hv hmt hvbase hm freshMember freshSucc freshCy freshCz freshG freshL freshY freshv freshm
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let G := pointGuard φ x
  let A := code (FOL.substAt φ x Peano.zero)
  let S := code (FOL.allAt x (paStep φ x))
  let D := candidateCode point bD p q u t l m r
  let B := uniformBaseCode t m (base+3) f
  let H := allCode Y (imp (candidateCode Y bD p q u t l m r) (allStepsCode Y t v m w p q f))
  let Γ := [D,S,A,G]
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have hS : Context Γ S := .hypothesis (by simp [Γ])
  have hA : Context Γ A := .hypothesis (by simp [Γ])
  have hG : Context Γ G := .hypothesis (by simp [Γ])
  have hB : Context Γ B := .mp hA (.mp hG (.closed hb))
  have hH : Context Γ H := .mp hS (.mp hG (.closed hs))
  exact .mp hH (.mp hB (.mp hd (.closed engine)))

end PASoundness.PAtoCompactFullInductionPointComposition

#print axioms PASoundness.PAtoCompactFullInductionPointComposition.full_point_of_engine
