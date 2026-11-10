import PASoundness.PAtoCompactCompositionSuppliedCombine
import PASoundness.PAtoCompactPartialCompositionInstantiate
import PASoundness.PAtoCompactCompositionForwardOld
import PASoundness.PAtoCompactCompositionForwardCases
import PASoundness.PAtoCompactCompositionForwardEndpointExists

/-! Uniform forward coverage for a supplied partial-composition successor.
The selected images, successor, pair, adjunction and old invariant remain the
literal `suppliedPremises` antecedent. This does not construct witnesses or
prove the backward direction, induction, graph collection or transitivity. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCompositionForwardAll
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactCompositionSuppliedVacuity PASoundness.PAtoCompactCompositionSuppliedCombine
open PASoundness.PAtoCompactPartialCompositionInstantiate PASoundness.PAtoCompactCompositionSelectedImages
open PASoundness.PAtoCompactCompositionForwardOld PASoundness.PAtoCompactCompositionForwardCases
open PASoundness.PAtoCompactCompositionForwardEndpointExists PASoundness.PAtoCompactCompositionAdjoinEdges
open PASoundness.PAtoCompactPartialCompositionOutputUnique
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A supplied partial-composition successor satisfies every guarded forward
coverage instance. The intermediate path witness remains existential. -/
def forward_all : KDerivation (imp suppliedPremises.encode forwardCoverage.encode) := by
  let U := suppliedPremises.encode
  let Q := both (member 0 2) (member 8 3)
  let P := path.encode
  let G := (graphFormula 17 2 3).encode
  let Γ := [U]
  have hlocal : Context Γ (imp Q (imp (both (member 13 2) P) G)) := by
    apply Context.deduction
    apply Context.deduction
    let Δ := [both (member 13 2) P,Q,U]
    have hnew : Context Δ (both (member 13 2) P) := Context.head _ _
    have hguard : Context Δ Q := .hypothesis (by simp [Δ])
    have hu : Context Δ U := .hypothesis (by simp [Δ])
    have hx : Context Δ (member 0 2) := Context.conjunctionLeft hguard
    have hz : Context Δ (member 8 3) := Context.conjunctionRight hguard
    have hn : Context Δ (member 13 2) := Context.conjunctionLeft hnew
    have hp : Context Δ P := Context.conjunctionRight hnew
    have himg1 : Context Δ firstImageBody.encode := Context.conjunctionLeft hu
    have htail := Context.conjunctionRight hu
    have himg2 : Context Δ secondImageBody.encode := Context.conjunctionLeft htail
    have htail := Context.conjunctionRight htail
    have hsucc : Context Δ (successorCode 10 13 15) := Context.conjunctionLeft htail
    have htail := Context.conjunctionRight htail
    have hpair : Context Δ (pairFormula 16 10 12).encode := Context.conjunctionLeft htail
    have htail := Context.conjunctionRight htail
    have hadj : Context Δ (PAtoCompactPointAdjoin.adjoinCode 9 16 17 18) := Context.conjunctionLeft htail
    have hold : Context Δ PAtoCompactPartialCompositionBase.partialComposition.encode := Context.conjunctionRight htail
    have hf : Context Δ firstUnique.encode := Context.conjunctionRight (Context.conjunctionRight himg1)
    have hs : Context Δ secondUnique.encode := Context.conjunctionRight (Context.conjunctionRight himg2)
    have holdpoint : Context Δ pointFormula.encode := .mp hold (.closed partial_composition_instance)
    rw [point_formula_code] at holdpoint
    have holdiff : Context Δ (both
        (imp (graphFormula 9 2 3).encode (both (member 10 2) P))
        (imp (both (member 10 2) P) (graphFormula 9 2 3).encode)) :=
      .mp (Context.conjunctionIntro hx hz) holdpoint
    have holdcov : Context Δ (imp (both (member 10 2) P) (graphFormula 9 2 3).encode) :=
      Context.conjunctionRight holdiff
    have holdcase : Context Δ (imp (member 10 2) (imp P G)) :=
      .mp holdcov (.mp hadj (.closed forward_old_closed))
    have hselected : Context Δ (graphFormula 17 10 12).encode :=
      .mp hpair (.mp hadj (.closed adjoin_selected_edge))
    have hnewcase : Context Δ (imp (equal 2 10) (imp P G)) := by
      apply Context.deduction
      let Ξ := equal 2 10 :: Δ
      have he : Context Ξ (equal 2 10) := Context.head _ _
      have hcontext : Context Ξ PAtoCompactCompositionPathVacuity.premises.encode :=
        Context.conjunctionIntro (Context.under hf _) (Context.conjunctionIntro
          (Context.under hs _) (Context.conjunctionIntro he
            (Context.conjunctionIntro (Context.under hz _) (Context.under hselected _))))
      exact .mp hcontext (.closed endpoint_path)
    have hcases : Context Δ (imp (member 13 2) (imp P G)) :=
      .mp hnewcase (.mp holdcase (.mp hsucc (.closed (forward_cases P G))))
    exact .mp hp (.mp hn hcases)
  have hv3 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 3 h)) := by
    intro h hh
    have he : h = U := by simpa [Γ] using hh
    subst h
    exact vacuity_3
  have hv2 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 2 h)) := by
    intro h hh
    have he : h = U := by simpa [Γ] using hh
    subst h
    exact vacuity_2
  have hall : Context Γ (allCode 2 (allCode 3 (imp Q (imp (both (member 13 2) P) G)))) :=
    Context.generalize 2 hv2 (Context.generalize 3 hv3 hlocal)
  apply Context.closeEmpty
  apply Context.deduction
  exact hall

theorem forward_all_certificate : theoremCode (certificate forward_all) =
    imp suppliedPremises.encode forwardCoverage.encode := certificate_correct forward_all

end PASoundness.PAtoCompactCompositionForwardAll

#print axioms PASoundness.PAtoCompactCompositionForwardAll.forward_all
#print axioms PASoundness.PAtoCompactCompositionForwardAll.forward_all_certificate
