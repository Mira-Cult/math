import PASoundness.PAtoCompactMemberCutSelectedTarget
import PASoundness.PAtoCompactMemberTargetSuffixExists

/-! A conditional finite-K collection of a target cut and suffix. The supplied
cut proof and same-graph suffix-equivalence proof remain explicit proof-data
inputs. This module does not construct the original isomorphism or either
input proof and does not establish addition output transport. -/
namespace PASoundness.PAtoCompactMemberChosenConditional
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactTermGraphBinderRange PASoundness.PAtoCompactMemberCutSelectedTarget
open PASoundness.PAtoCompactMemberTargetSuffixExists
set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The target cut 41 remains a member of 8, is linked to the actual old cut
33 by the original graph60, and is allocated-equivalent to 33. -/
def cutBody : Formula := namedBoth (namedBoth (.member 8 41) (graphFormula 60 33 41))
  (equivAt 100 33 41)

private theorem cut_free_38 : 38 ∉ cutBody.free := by
  have hm : 38 ∉ ({8,41} : Finset Nat) := by decide
  have hg : 38 ∉ (graphFormula 60 33 41).free := by decide
  have he : 38 ∉ (equivAt 100 33 41).free := by
    intro h
    have hnames := equivAt_free 100 33 41 h
    simp only [Finset.mem_insert,Finset.mem_singleton] at hnames
    rcases hnames with hnames | hnames <;> omega
  intro h
  simp only [cutBody,namedBoth,Formula.free,Finset.union_empty,Finset.empty_union,Finset.mem_union] at h
  tauto

private theorem chosen_free_38 : 38 ∉ chosen.free := by
  simp [chosen, Formula.free]

private theorem chosen_free_41 : 41 ∉ chosen.free := by
  simp [chosen, Formula.free]

/-- Given a selected cut proof and a suffix-equivalence proof under the same
cut body and original guard, construct one pair of target witnesses. Guard
freshness is explicit; the denoted objects may coincide. -/
def collect_selected (g : Formula) (hg38 : 38 ∉ g.free) (hg41 : 41 ∉ g.free)
    (cutProof : KDerivation (imp g.encode (existsCode 41 cutBody.encode)))
    (suffixProof : KDerivation (imp g.encode (imp cutBody.encode
      (imp PAtoCompactMemberCutRawTargetIntro.targetSuffix.encode (equivAt 100 34 38).encode)))) :
    KDerivation (imp g.encode chosen.encode) := by
  let Γ := [g.encode]
  have hg : Context Γ g.encode := .head _ _
  have hcut : Context Γ (existsCode 41 cutBody.encode) := .mp hg (.closed cutProof)
  have hcutLocal : Context (cutBody.encode :: Γ) chosen.encode := by
    let Δ := cutBody.encode :: Γ
    have hc : Context Δ cutBody.encode := .head _ _
    have hg' : Context Δ g.encode := .under hg _
    have he : Context Δ (equivAt 100 33 41).encode := Context.conjunctionRight hc
    have hp := Context.conjunctionLeft hc
    have hm : Context Δ (member 8 41) := Context.conjunctionLeft hp
    have hpoint : Context (PAtoCompactMemberCutRawTargetIntro.targetSuffix.encode :: Δ) chosen.encode := by
      let Ξ := PAtoCompactMemberCutRawTargetIntro.targetSuffix.encode :: Δ
      have hs : Context Ξ PAtoCompactMemberCutRawTargetIntro.targetSuffix.encode := .head _ _
      have hg'' : Context Ξ g.encode := .under hg' _
      have hc' : Context Ξ cutBody.encode := .under hc _
      have he' : Context Ξ (equivAt 100 33 41).encode := .under he _
      have hm' : Context Ξ (member 8 41) := .under hm _
      have hes : Context Ξ (equivAt 100 34 38).encode :=
        .mp hs (.mp hc' (.mp hg'' (.closed suffixProof)))
      have hb : Context Ξ chosenBody.encode := by
        have h := Context.conjunctionIntro he' (Context.conjunctionIntro hes
          (Context.conjunctionIntro hm' hs))
        simpa only [chosenBody,namedBoth,Formula.not,Formula.encode,both,neg] using h
      have h38 : Context Ξ (existsCode 38 chosenBody.encode) :=
        .mp hb (.closed (existsIntroduce 38 chosenBody (by decide)))
      have h41 := existsIntroduce 41 (.ex 38 chosenBody) (by decide)
      have h := Context.mp h38 (.closed h41)
      simpa only [chosen,Formula.encode] using h
    have hv38 : ∀ h, h ∈ Δ → KDerivation (imp h (allCode 38 h)) := by
      intro h hh
      simp only [Δ,Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
      by_cases he : h = cutBody.encode
      · subst h
        exact free_vacuity 38 cutBody cut_free_38
      have he : h = g.encode := by simp_all
      subst h
      exact free_vacuity 38 g hg38
    have hall38 := Context.generalize 38 hv38 (Context.deduction hpoint)
    exact Context.existsElim (free_vacuity 38 chosen chosen_free_38) hall38
      (.closed target_suffix_exists)
  have hv41 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 41 h)) := by
    intro h hh
    have he : h = g.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 41 g hg41
  have hall41 := Context.generalize 41 hv41 (Context.deduction hcutLocal)
  apply Context.closeEmpty
  apply Context.deduction
  exact Context.existsElim (free_vacuity 41 chosen chosen_free_41) hall41 hcut

theorem collect_selected_certificate (g : Formula) (hg38 : 38 ∉ g.free) (hg41 : 41 ∉ g.free)
    (cutProof : KDerivation (imp g.encode (existsCode 41 cutBody.encode)))
    (suffixProof : KDerivation (imp g.encode (imp cutBody.encode
      (imp PAtoCompactMemberCutRawTargetIntro.targetSuffix.encode (equivAt 100 34 38).encode)))) :
    theoremCode (certificate (collect_selected g hg38 hg41 cutProof suffixProof)) =
      imp g.encode chosen.encode := certificate_correct _
end PASoundness.PAtoCompactMemberChosenConditional

#print axioms PASoundness.PAtoCompactMemberChosenConditional.collect_selected
#print axioms PASoundness.PAtoCompactMemberChosenConditional.collect_selected_certificate
