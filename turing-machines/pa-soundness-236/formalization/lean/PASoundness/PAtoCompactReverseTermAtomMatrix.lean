import PASoundness.PAtoCompactUnaryGraphFunctionalityFull
import PASoundness.PAtoCompactEquivMultiAlpha
import PASoundness.PAtoCompactDynamicTransitivityFinal
import PASoundness.PAtoCompactCandidateDynamicReflexivity
import PASoundness.PAtoCompactVacuousEqualityAlignment

/-! Reverse substitution at an equality matrix, retaining a graph of the
substituted unary term. All proof data are finite K derivations. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactReverseTermAtomMatrix
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactVacuousEqualityAlignment
open PASoundness.PAtoCompactAllTermTransport PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactEquivMultiAlpha PASoundness.PAtoCompactDynamicTransitivityFinal
open PASoundness.PAtoCompactCandidateDynamicReflexivity
open PASoundness.PAtoCompactUnaryGraphFunctionalityFull PASoundness.PAtoCompactUnaryTermTransport
open PASoundness.PAtoCompactSuccTermTotality

/-- Given a guard and two graphs of the same unary term at q and a, replace
the left matrix witness a by q. The unchanged right term is arbitrary. -/
noncomputable def reverse_matrix (t s : Peano.Term) (ht : UnaryTerm t)
    (guard : CompactNamed.Formula) (q a r b oldRight newRight oldEq newEq : Nat)
    (hq : q < b) (ha : a < b)
    (htb : ∀ v ∈ t.varFinset, v < b) (hgb : ∀ v ∈ guard.free, v < b)
    (hguard : ∀ v ∈ t.varFinset,
      KDerivation (imp guard.encode (domainAt b v).encode))
    (hrOld : r < oldRight) (hrNew : r < newRight)
    (hsOld : ∀ v ∈ s.varFinset, v < oldRight)
    (hsNew : ∀ v ∈ s.varFinset, v < newRight)
    (haOldEq : a < oldEq+2) (hrOldEq : r < oldEq+2)
    (hqNewEq : q < newEq+2) (haNewEq : a < newEq+2) (hrNewEq : r < newEq+2) :
    KDerivation (imp guard.encode (imp (termGraph id t q b).encode
      (imp (matrix id t s a r b oldRight oldEq).encode
        (matrix id (.var q) s q r b newRight newEq).encode))) := by
  have hfun := unary_functional id guard ht b q a
    (by intro v hv; simpa only [id_eq] using htb v hv) hgb
    (by intro v hv; simpa only [id_eq] using hguard v hv) hq ha
  have heq1 := (equivAt_base_alpha b newEq q a (by omega) (by omega)
    hqNewEq haNewEq).forward
  have heq2 := (equivAt_base_alpha oldEq newEq a r haOldEq hrOldEq
    haNewEq hrNewEq).forward
  have hs := (termGraph_base_transport id s oldRight newRight r hrOld hrNew
    (by intro v hv; simpa only [id_eq] using hsOld v hv)
    (by intro v hv; simpa only [id_eq] using hsNew v hv)).1
  have hdom := domainAt_transport b newEq q (by omega) (by omega)
  have htrans := dynamic_transitivity newEq q a r hqNewEq haNewEq hrNewEq
  have hrefl := dynamic_reflexive b q (by omega)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let T := (termGraph id t q b).encode
  let M := (matrix id t s a r b oldRight oldEq).encode
  let Γ := [M,T,guard.encode]
  have hm : Context Γ M := Context.head _ _
  have htq : Context Γ T := .hypothesis (by simp [Γ])
  have hg : Context Γ guard.encode := .hypothesis (by simp [Γ])
  have hm' : Context Γ (both (termGraph id t a b).encode
      (both (termGraph id s r oldRight).encode (equivAt oldEq a r).encode)) := by
    simpa [M, matrix, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hm
  have hta := Context.conjunctionLeft hm'
  have hrest := Context.conjunctionRight hm'
  have hsr := Context.conjunctionLeft hrest
  have har := Context.conjunctionRight hrest
  have hqa : Context Γ (equivAt b q a).encode := .mp hta (.mp htq (.mp hg (.closed hfun)))
  have hdq : Context Γ (domainAt b q).encode := .mp htq (.closed (termGraph_domain id t q b))
  have hqq : Context Γ (equivAt b q q).encode := .mp hdq (.closed hrefl)
  have hvar : Context Γ (termGraph id (.var q) q b).encode := by
    change Context Γ (both (domainAt b q).encode (equivAt b q q).encode)
    exact Context.conjunctionIntro hdq hqq
  have hqe : Context Γ (equivAt newEq q a).encode := .mp hqa (.closed heq1)
  have hae : Context Γ (equivAt newEq a r).encode := .mp har (.closed heq2)
  have hde : Context Γ (domainAt newEq q).encode := .mp hdq (.closed hdom)
  have hqr : Context Γ (equivAt newEq q r).encode := .mp hae (.mp hqe (.mp hde (.closed htrans)))
  have hsr' : Context Γ (termGraph id s r newRight).encode := .mp hsr (.closed hs)
  have hout := Context.conjunctionIntro hvar (Context.conjunctionIntro hsr' hqr)
  simpa [Γ, M, T, matrix, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hout


theorem reverse_matrix_certificate (t s : Peano.Term) (ht : UnaryTerm t)
    (guard : CompactNamed.Formula) (q a r b oldRight newRight oldEq newEq : Nat)
    (hq : q < b) (ha : a < b)
    (htb : ∀ v ∈ t.varFinset, v < b) (hgb : ∀ v ∈ guard.free, v < b)
    (hguard : ∀ v ∈ t.varFinset,
      KDerivation (imp guard.encode (domainAt b v).encode))
    (hrOld : r < oldRight) (hrNew : r < newRight)
    (hsOld : ∀ v ∈ s.varFinset, v < oldRight)
    (hsNew : ∀ v ∈ s.varFinset, v < newRight)
    (haOldEq : a < oldEq+2) (hrOldEq : r < oldEq+2)
    (hqNewEq : q < newEq+2) (haNewEq : a < newEq+2) (hrNewEq : r < newEq+2) :
    theoremCode (certificate (reverse_matrix t s ht guard q a r b oldRight newRight oldEq newEq
      hq ha htb hgb hguard hrOld hrNew hsOld hsNew haOldEq hrOldEq hqNewEq haNewEq hrNewEq)) =
      imp guard.encode (imp (termGraph id t q b).encode
        (imp (matrix id t s a r b oldRight oldEq).encode
          (matrix id (.var q) s q r b newRight newEq).encode)) := certificate_correct _

end PASoundness.PAtoCompactReverseTermAtomMatrix

#print axioms PASoundness.PAtoCompactReverseTermAtomMatrix.reverse_matrix

#print axioms PASoundness.PAtoCompactReverseTermAtomMatrix.reverse_matrix_certificate
