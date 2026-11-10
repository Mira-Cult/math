import PASoundness.PAtoCompactAdditionOperationGuarded
import PASoundness.PAtoCompactSuccTermTotality
import PASoundness.PAtoCompactTermSubstBinaryStep
import PASoundness.PAtoCompactGuardBaseTransport

/-! Extract every candidate premise for addition congruence from the four
actual child graphs and two actual parent graphs. -/
namespace PASoundness.PAtoCompactAdditionGraphOperationPoint

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactTermSubstBinaryStep PASoundness.PAtoCompactSuccTermTotality
open PASoundness.PAtoCompactGuardBaseTransport

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def guard {α : Type} (v : α → Nat) (t u : Peano.language.Term α) (b c p q e : Nat) : Formula :=
  namedBoth (termGraph v t b (b+64)) (namedBoth (termGraph v u (b+1) (b+64+termCost t))
    (namedBoth (termGraph v t c (c+64)) (namedBoth (termGraph v u (c+1) (c+64+termCost t))
      (namedBoth (termGraph v (binaryTerm true t u) p b) (namedBoth (termGraph v (binaryTerm true t u) q c)
        (namedBoth (equivAt e b c) (namedBoth (equivAt e (b+1) (c+1))
          (namedBoth (addAt b b (b+1) p) (addAt c c (c+1) q)))))))))

/-- The actual graph premises, two child-output equivalences and two
addition relations supply every guarded operation premise. -/
def graph_operation_point {α : Type} (v : α → Nat) (t u : Peano.language.Term α)
    (b c p q e f : Nat) (hbe : b+1 < e+2) (hce : c+1 < e+2)
    (hpe : p < e+2) (hqe : q < e+2) (hpb : p < b+2) (hqc : q < c+2)
    (hpf : p < f+2) (hqf : q < f+2) :
    KDerivation (imp (guard v t u b c p q e).encode (equivAt f p q).encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [(guard v t u b c p q e).encode]
  have hg : Context Γ (guard v t u b c p q e).encode := .head _ _
  have hl1 : Context Γ (termGraph v t b (b+64)).encode := Context.conjunctionLeft hg
  have hr := Context.conjunctionRight hg
  have hr1 : Context Γ (termGraph v u (b+1) (b+64+termCost t)).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hl2 : Context Γ (termGraph v t c (c+64)).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hr2 : Context Γ (termGraph v u (c+1) (c+64+termCost t)).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hp1 : Context Γ (termGraph v (binaryTerm true t u) p b).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hp2 : Context Γ (termGraph v (binaryTerm true t u) q c).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have he1 : Context Γ (equivAt e b c).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have he2 : Context Γ (equivAt e (b+1) (c+1)).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have ha1 : Context Γ (addAt b b (b+1) p).encode := Context.conjunctionLeft hr
  have ha2 : Context Γ (addAt c c (c+1) q).encode := Context.conjunctionRight hr
  have hdL1 : Context Γ (domainAt (b+64) b).encode := .mp hl1 (.closed (termGraph_domain v t b (b+64)))
  have hdR1 : Context Γ (domainAt (b+64+termCost t) (b+1)).encode :=
    .mp hr1 (.closed (termGraph_domain v u (b+1) (b+64+termCost t)))
  have hdL2 : Context Γ (domainAt (c+64) c).encode := .mp hl2 (.closed (termGraph_domain v t c (c+64)))
  have hdR2 : Context Γ (domainAt (c+64+termCost t) (c+1)).encode :=
    .mp hr2 (.closed (termGraph_domain v u (c+1) (c+64+termCost t)))
  have hdP : Context Γ (domainAt b p).encode := .mp hp1 (.closed (termGraph_domain v (binaryTerm true t u) p b))
  have hdQ : Context Γ (domainAt c q).encode := .mp hp2 (.closed (termGraph_domain v (binaryTerm true t u) q c))
  have dx : Context Γ (domainAt e b).encode := .mp hdL1 (.closed (domainAt_transport (b+64) e b (by omega) (by omega)))
  have dy : Context Γ (domainAt e (b+1)).encode := .mp hdR1 (.closed (domainAt_transport (b+64+termCost t) e (b+1) (by omega) (by omega)))
  have du : Context Γ (domainAt e c).encode := .mp hdL2 (.closed (domainAt_transport (c+64) e c (by omega) (by omega)))
  have dv : Context Γ (domainAt e (c+1)).encode := .mp hdR2 (.closed (domainAt_transport (c+64+termCost t) e (c+1) (by omega) (by omega)))
  have dz : Context Γ (domainAt e p).encode := .mp hdP (.closed (domainAt_transport b e p (by omega) (by omega)))
  have dw : Context Γ (domainAt e q).encode := .mp hdQ (.closed (domainAt_transport c e q (by omega) (by omega)))
  have hop : Context Γ (PASoundness.PAtoCompactAdditionOperationGuarded.guard e b c b (b+1) p c (c+1) q).encode :=
    Context.conjunctionIntro dx (Context.conjunctionIntro dy (Context.conjunctionIntro du
      (Context.conjunctionIntro dv (Context.conjunctionIntro dz (Context.conjunctionIntro dw
        (Context.conjunctionIntro he1 (Context.conjunctionIntro he2 (Context.conjunctionIntro ha1 ha2))))))))
  have h := PASoundness.PAtoCompactAdditionOperationGuarded.addition_operation_guarded e b c f b (b+1) p c (c+1) q
    (by omega) hbe hpe (by omega) hce hqe (by omega) (by omega) hpb (by omega) (by omega) hqc hpf hqf
  exact .mp hop (.closed h)

theorem graph_operation_point_certificate {α : Type} (v : α → Nat) (t u : Peano.language.Term α)
    (b c p q e f : Nat) (hbe : b+1 < e+2) (hce : c+1 < e+2)
    (hpe : p < e+2) (hqe : q < e+2) (hpb : p < b+2) (hqc : q < c+2)
    (hpf : p < f+2) (hqf : q < f+2) :
    theoremCode (certificate (graph_operation_point v t u b c p q e f hbe hce hpe hqe hpb hqc hpf hqf)) =
      imp (guard v t u b c p q e).encode (equivAt f p q).encode := certificate_correct _

end PASoundness.PAtoCompactAdditionGraphOperationPoint

#print axioms PASoundness.PAtoCompactAdditionGraphOperationPoint.guard
#print axioms PASoundness.PAtoCompactAdditionGraphOperationPoint.graph_operation_point
#print axioms PASoundness.PAtoCompactAdditionGraphOperationPoint.graph_operation_point_certificate
