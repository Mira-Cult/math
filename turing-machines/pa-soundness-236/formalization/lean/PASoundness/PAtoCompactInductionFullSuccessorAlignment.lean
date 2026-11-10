import PASoundness.PAtoCompactScopedSuccessorComplete
import PASoundness.PAtoCompactInductionPredecessorDomain
import PASoundness.PAtoCompactPAInductionOutputGraph
import PASoundness.PAtoCompactInductionPredicateAlignment

/-! Finite K successor-substitution alignment for an arbitrary PA induction
predicate. Candidate output and the predecessor core supply the domain guard
for the predecessor and its successor graph; no semantic soundness or
substitution-compatibility premise is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactInductionFullSuccessorAlignment
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactHilbertBasis
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactUnaryTermTransport PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactUniformStep
open PASoundness.PAtoCompactDirectGeneralization PASoundness.PAtoCompactGuardedGeneralizationAlignment
open PASoundness.PAtoCompactInductionPredecessorDomain PASoundness.PAtoCompactPAInductionOutputGraph
open PASoundness.PAtoCompactInductionPredicateAlignment
open PASoundness.PAtoCompactScopedSuccessorComplete PASoundness.PAtoCompactTermSubstSuccessorInduction

/-- The actual PA successor step aligns with the opened named predicate for
any PA formula. Explicit allocation and freshness conditions remain, but the
caller supplies no finite K proof data. -/
noncomputable def full_successor_alignment
    (φ : Peano.Formula) (x t Y y z w p q d u k c h g v r s graphBase : Nat)
    (htop : topName x φ < t) (hzt : z < t)
    (hy : y < graphBase) (hz : z < graphBase)
    (hwy : w ≠ y) (hwz : w ≠ z)
    (fresh : [z,y,d,p,q,v,u,k,c,h,g,r,s].Nodup) :
    KDerivation (imp (guardFormula (Peano.inductionAxiom φ x)).encode
      (imp (candidateCode z d p q u k c h g)
        (imp (predecessorCore Y y z w p q)
          (imp (code (FOL.substAt φ x (Peano.succ (.var y))))
            (replace t z (scopeAt φ x t)).encode)))) := by
  have hud : ∀ a ∈ ((.var y : Peano.Term).varFinset), a < graphBase := by
    intro a ha
    have ha' : a = y := by simpa [Term.varFinset] using ha
    simpa [ha'] using hy
  have hdom : ∀ a ∈ ((.var y : Peano.Term).varFinset),
      KDerivation (imp (domainAt graphBase y).encode (domainAt graphBase a).encode) := by
    intro a ha
    have ha' : a = y := by simpa [Term.varFinset] using ha
    subst a
    exact identity _
  have hsub := (formula_successor_substitution (domainAt graphBase y) (.var y)
    (UnaryTerm.var y) x z graphBase hz hud hdom φ).2
  have hpred := predecessor_domain_from_output graphBase Y y z w p q d u k c h g v r s
    (by omega) hwy hwz fresh
  have hgraph := output_candidate_term_graph graphBase Y y z w p q d u k c h g v r s
    hy hz hwy hwz fresh
  have hfinal := (named_predicate_alignment φ x t z htop hzt).2
  let G := (guardFormula (Peano.inductionAxiom φ x)).encode
  let C := candidateCode z d p q u k c h g
  let P := predecessorCore Y y z w p q
  let X := (termGraph id (Peano.succ (.var y)) z graphBase).encode
  let S := code (FOL.substAt φ x (Peano.succ (.var y)))
  let H := (andF (domainAt graphBase y) (termGraph id (Peano.succ (.var y)) z graphBase)).encode
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [S,P,C,G]
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hd : Context Γ (domainAt graphBase y).encode := .mp hp (.mp hc (.closed hpred))
  have hx : Context Γ X := .mp hp (.mp hc (.closed hgraph))
  have hH : Context Γ H := by
    have hh := Context.conjunctionIntro hd hx
    simpa [H, andF, CompactNamed.Formula.encode, CompactNamed.Formula.not, both, neg] using hh
  have hsub' : KDerivation (imp H (imp S (code (FOL.substAt φ x (.var z))))) := by
    simpa only [H, S, retained, succTerm, Peano.succ, code] using hsub
  have hv : Context Γ (code (FOL.substAt φ x (.var z))) :=
    .mp hs (.mp hH (.closed hsub'))
  exact .mp hv (.closed hfinal)

theorem full_successor_alignment_certificate
    (φ : Peano.Formula) (x t Y y z w p q d u k c h g v r s graphBase : Nat)
    (htop : topName x φ < t) (hzt : z < t)
    (hy : y < graphBase) (hz : z < graphBase)
    (hwy : w ≠ y) (hwz : w ≠ z)
    (fresh : [z,y,d,p,q,v,u,k,c,h,g,r,s].Nodup) :
    theoremCode (certificate (full_successor_alignment φ x t Y y z w p q d u k c h g v r s graphBase
      htop hzt hy hz hwy hwz fresh)) =
      imp (guardFormula (Peano.inductionAxiom φ x)).encode
        (imp (candidateCode z d p q u k c h g) (imp (predecessorCore Y y z w p q)
          (imp (code (FOL.substAt φ x (Peano.succ (.var y))))
            (replace t z (scopeAt φ x t)).encode))) := certificate_correct _
end PASoundness.PAtoCompactInductionFullSuccessorAlignment

#print axioms PASoundness.PAtoCompactInductionFullSuccessorAlignment.full_successor_alignment
#print axioms PASoundness.PAtoCompactInductionFullSuccessorAlignment.full_successor_alignment_certificate
