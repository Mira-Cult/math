import PASoundness.PAtoCompactQFreeUnaryFragment
import PASoundness.PAtoCompactInductionAugmentedGuard
import PASoundness.PAtoCompactInductionPredecessorDomain
import PASoundness.PAtoCompactPAInductionOutputGraph
import PASoundness.PAtoCompactInductionPredicateAlignment

/-! Actual successor-substitution alignment for the restricted quantifier-free
fragment, in the guarded PA induction step. The predecessor's candidate guard
is derived from the output candidate and the predecessor core; the PA guard is
then augmented to cover the fresh input variable y. General equalities and
quantifiers are not covered. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactInductionQFreeSuccessorAlignment
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactUnaryTermTransport PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactUniformStep
open PASoundness.PAtoCompactDirectGeneralization PASoundness.PAtoCompactGuardedGeneralizationAlignment
open PASoundness.PAtoCompactQFreeUnaryFragment PASoundness.PAtoCompactInductionAugmentedGuard
open PASoundness.PAtoCompactInductionPredecessorDomain PASoundness.PAtoCompactPAInductionOutputGraph
open PASoundness.PAtoCompactInductionPredicateAlignment

/-- The scoped successor alignment is a finite K derivation for a formula in
the displayed restricted fragment. All names and allocation conditions are
explicit; no substitution-compatibility proof is supplied as an input. -/
noncomputable def qfree_successor_alignment
    (φ : Peano.Formula) (x t Y y z w p q d u k c h g v r s graphBase : Nat)
    (frag : Fragment x φ) (htop : topName x φ < t) (hzt : z < t)
    (hy : y < graphBase) (hz : z < graphBase)
    (hguard : guardBase (augmented (Peano.inductionAxiom φ x) y) ≤ graphBase)
    (hwy : w ≠ y) (hwz : w ≠ z)
    (fresh : [z,y,d,p,q,v,u,k,c,h,g,r,s].Nodup) :
    KDerivation (imp (guardFormula (Peano.inductionAxiom φ x)).encode
      (imp (candidateCode z d p q u k c h g)
        (imp (predecessorCore Y y z w p q)
          (imp (code (FOL.substAt φ x (Peano.succ (.var y))))
            (replace t z (scopeAt φ x t)).encode)))) := by
  let A := augmented (Peano.inductionAxiom φ x) y
  have hcover : ∀ a ∈ (Peano.succ (.var y)).varFinset, a ∈ A.freeVarFinset := by
    intro a ha
    have ha' : a = y := by
      simpa [Peano.succ, Term.varFinset] using ha
    subst a
    change y ∈ (augmented (Peano.inductionAxiom φ x) y).freeVarFinset
    rw [augmented_free]
    simp
  have hunary : UnaryTerm (Peano.succ (.var y)) := UnaryTerm.succ (UnaryTerm.var y)
  have hsub := (fragment_substitution A x (Peano.succ (.var y)) hunary z graphBase hguard hz hcover frag).2
  have hdom := predecessor_domain_from_output graphBase Y y z w p q d u k c h g v r s
    (by omega) hwy hwz fresh
  have hgraph := output_candidate_term_graph graphBase Y y z w p q d u k c h g v r s
    hy hz hwy hwz fresh
  have haug := augmented_guard (Peano.inductionAxiom φ x) y graphBase (by omega)
  have hfinal := (named_predicate_alignment φ x t z htop hzt).2
  let G := (guardFormula (Peano.inductionAxiom φ x)).encode
  let C := candidateCode z d p q u k c h g
  let P := predecessorCore Y y z w p q
  let X := (termGraph id (Peano.succ (.var y)) z graphBase).encode
  let S := code (FOL.substAt φ x (Peano.succ (.var y)))
  let H := (andF (guardFormula A) (termGraph id (Peano.succ (.var y)) z graphBase)).encode
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [S,P,C,G]
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hd : Context Γ (domainAt graphBase y).encode := .mp hp (.mp hc (.closed hdom))
  have hA : Context Γ (guardFormula A).encode := .mp hd (.mp hg (.closed haug))
  have hx : Context Γ X := .mp hp (.mp hc (.closed hgraph))
  have hH : Context Γ H := by
    have hh := Context.conjunctionIntro hA hx
    simpa [H, andF, CompactNamed.Formula.encode, CompactNamed.Formula.not, both, neg] using hh
  have hv : Context Γ (code (FOL.substAt φ x (.var z))) := .mp hs (.mp hH (.closed hsub))
  exact .mp hv (.closed hfinal)

theorem qfree_successor_alignment_certificate
    (φ : Peano.Formula) (x t Y y z w p q d u k c h g v r s graphBase : Nat)
    (frag : Fragment x φ) (htop : topName x φ < t) (hzt : z < t)
    (hy : y < graphBase) (hz : z < graphBase)
    (hguard : guardBase (augmented (Peano.inductionAxiom φ x) y) ≤ graphBase)
    (hwy : w ≠ y) (hwz : w ≠ z)
    (fresh : [z,y,d,p,q,v,u,k,c,h,g,r,s].Nodup) :
    theoremCode (certificate (qfree_successor_alignment φ x t Y y z w p q d u k c h g v r s graphBase
      frag htop hzt hy hz hguard hwy hwz fresh)) =
      imp (guardFormula (Peano.inductionAxiom φ x)).encode
        (imp (candidateCode z d p q u k c h g) (imp (predecessorCore Y y z w p q)
          (imp (code (FOL.substAt φ x (Peano.succ (.var y))))
            (replace t z (scopeAt φ x t)).encode))) := certificate_correct _
end PASoundness.PAtoCompactInductionQFreeSuccessorAlignment

#print axioms PASoundness.PAtoCompactInductionQFreeSuccessorAlignment.qfree_successor_alignment
#print axioms PASoundness.PAtoCompactInductionQFreeSuccessorAlignment.qfree_successor_alignment_certificate
