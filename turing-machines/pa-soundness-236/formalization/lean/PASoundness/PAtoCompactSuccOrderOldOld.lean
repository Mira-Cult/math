import PASoundness.PAtoCompactSuccCleanEndpoint
import PASoundness.PAtoCompactSuccCongruenceOrderAlpha
import PASoundness.PAtoCompactSuccOrderPointShape

/-! Pointwise old/old case for conditional successor order preservation. The
old order and clean graph are explicit hypotheses; this does not establish
edge splitting, graph existence or the full quotient congruence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccOrderOldOld
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrderIsoInstance
open PASoundness.PAtoCompactSuccCongruenceData PASoundness.PAtoCompactSuccCongruenceOrderAlpha
open PASoundness.PAtoCompactSuccCleanEndpoint PASoundness.PAtoCompactSuccOrderPointShape

/-- Two old graph edges satisfy the exact successor-order point comparison. -/
def old_old : KDerivation (imp oldOrderFresh.encode (imp cleanGraph
    (imp (graphFormula 6 2 3).encode (imp (graphFormula 6 4 5).encode comparison)))) := by
  let O := oldOrderFresh.encode
  let C := cleanGraph
  let G23 := (graphFormula 6 2 3).encode
  let G45 := (graphFormula 6 4 5).encode
  let Γ := [G45,G23,C,O]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have ho : Context Γ O := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hg23 : Context Γ G23 := .hypothesis (by simp [Γ])
  have hg45 : Context Γ G45 := .hypothesis (by simp [Γ])
  have he23 : Context Γ (both (member 0 2) (member 1 3)) :=
    .mp hg23 (.mp hc (.closed (clean_endpoints 2 3 (by decide))))
  have he45 : Context Γ (both (member 0 4) (member 1 5)) :=
    .mp hg45 (.mp hc (.closed (clean_endpoints 4 5 (by decide))))
  have hmatrix : Context Γ orderMatrix.encode :=
    .mp (.mp ho (.closed order_unalpha)) (.closed order_instance)
  change Context Γ (imp (both (member 0 2) (both (member 0 4)
    (both (member 1 3) (both (member 1 5) (both G23 G45))))) comparison) at hmatrix
  have hguards : Context Γ (both (member 0 2) (both (member 0 4)
    (both (member 1 3) (both (member 1 5) (both G23 G45))))) :=
    Context.conjunctionIntro (Context.conjunctionLeft he23)
      (Context.conjunctionIntro (Context.conjunctionLeft he45)
        (Context.conjunctionIntro (Context.conjunctionRight he23)
          (Context.conjunctionIntro (Context.conjunctionRight he45)
            (Context.conjunctionIntro hg23 hg45))))
  exact .mp hguards hmatrix

theorem old_old_certificate : theoremCode (certificate old_old) =
    imp oldOrderFresh.encode (imp cleanGraph
      (imp (graphFormula 6 2 3).encode (imp (graphFormula 6 4 5).encode comparison))) :=
  certificate_correct old_old

end PASoundness.PAtoCompactSuccOrderOldOld

#print axioms PASoundness.PAtoCompactSuccOrderOldOld.old_old
#print axioms PASoundness.PAtoCompactSuccOrderOldOld.old_old_certificate
