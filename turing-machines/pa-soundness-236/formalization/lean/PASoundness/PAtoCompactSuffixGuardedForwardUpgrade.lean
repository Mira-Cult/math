import PASoundness.PAtoCompactCommonSourceSpanImages
import PASoundness.PAtoCompactFreeVacuity

/-! Widen a forward-bijection clause from a suffix to its containing whole,
provided the graph is clean into the suffix on common-source inputs. This is a
finite K proof-data construction. The suffix containment and graph-clean
conditions remain object-level antecedents; neither is constructed here.
No candidate condition on the suffix or whole is used. -/
namespace PASoundness.PAtoCompactSuffixGuardedForwardUpgrade

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactCommonSourceSpanImages PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactTransitiveWitness

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def oldUniqueBody : Formula := .imp
  (namedBoth (.member 31 4) (graphFormula 6 2 4)) (.equal 4 3)
private def newUniqueBody : Formula := .imp
  (namedBoth (.member 0 4) (graphFormula 6 2 4)) (.equal 4 3)

def suffixImage : Formula := namedBoth (.member 31 3)
  (namedBoth (graphFormula 6 2 3) (.all 4 oldUniqueBody))

def suffixForwardBody : Formula := .imp (.member 1 2) (.ex 3 suffixImage)
def suffixForward : Formula := .all 2 suffixForwardBody

def contained : Formula := .all 4 (.imp (.member 31 4) (.member 0 4))
def graphClean : Formula := .all 2 (.all 4
  (.imp (.member 1 2) (.imp (graphFormula 6 2 4) (.member 31 4))))

private def subsetAtThree : KDerivation (imp contained.encode (imp (member 31 3) (member 0 3))) := by
  let body : Formula := .imp (.member 31 4) (.member 0 4)
  have hi := universalInstance 4 3 body (by decide) (by decide) (by decide)
  have he : replace 4 3 body = .imp (.member 31 3) (.member 0 3) := by decide
  rw [he] at hi
  simpa only [contained, body, Formula.encode] using hi

private def cleanAtPoint : KDerivation (imp graphClean.encode
    (imp (member 1 2) (imp (graphFormula 6 2 4).encode (member 31 4)))) := by
  let body : Formula := .imp (.member 1 2) (.imp (graphFormula 6 2 4) (.member 31 4))
  have h2 := allSpecialize 2 (.all 4 body) (by decide)
  have h4 := allSpecialize 4 body (by decide)
  have h := compose h2 h4
  simpa only [graphClean, body, Formula.encode] using h

/-- A selected suffix image remains a unique image when uniqueness is tested
against the whole, because every competing graph edge is clean into suffix. -/
def upgrade_image : KDerivation (imp contained.encode (imp graphClean.encode
    (imp (member 1 2) (imp suffixImage.encode firstTemplate.encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [suffixImage.encode,member 1 2,graphClean.encode,contained.encode]
  have hi : Context Γ suffixImage.encode := .head _ _
  have hc : Context Γ graphClean.encode := .hypothesis (by simp [Γ])
  have hs : Context Γ contained.encode := .hypothesis (by simp [Γ])
  have hsource : Context Γ (member 1 2) := .hypothesis (by simp [Γ])
  have hm31 : Context Γ (member 31 3) := Context.conjunctionLeft hi
  have ht := Context.conjunctionRight hi
  have he : Context Γ (graphFormula 6 2 3).encode := Context.conjunctionLeft ht
  have hu : Context Γ (allCode 4 oldUniqueBody.encode) := Context.conjunctionRight ht
  have hm0 : Context Γ (member 0 3) := .mp hm31 (.mp hs (.closed subsetAtThree))
  have hpoint : Context Γ newUniqueBody.encode := by
    apply Context.deduction
    let D := both (member 0 4) (graphFormula 6 2 4).encode
    let Δ := [D,suffixImage.encode,member 1 2,graphClean.encode,contained.encode]
    have hd : Context Δ D := .head _ _
    have hedge : Context Δ (graphFormula 6 2 4).encode := Context.conjunctionRight hd
    have hmem : Context Δ (member 31 4) :=
      .mp hedge (.mp (.under hsource _) (.mp (.under hc _) (.closed cleanAtPoint)))
    have hu' : Context Δ (imp (both (member 31 4) (graphFormula 6 2 4).encode) (equal 4 3)) :=
      .mp (.under hu _) (.closed (allSpecialize 4 oldUniqueBody (by decide)))
    exact .mp (Context.conjunctionIntro hmem hedge) hu'
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 4 h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases hI : h = suffixImage.encode
    · subst h; exact free_vacuity 4 suffixImage (by decide)
    · have hrest := hh.resolve_left hI
      by_cases hM : h = member 1 2
      · subst h; exact (Formula.member 1 2).vacuity 4 (by decide)
      · have hrest := hrest.resolve_left hM
        by_cases hC : h = graphClean.encode
        · subst h; exact free_vacuity 4 graphClean (by decide)
        · have hS : h = contained.encode := hrest.resolve_left hC
          subst h; exact free_vacuity 4 contained (by decide)
  have hwhole : Context Γ (allCode 4 newUniqueBody.encode) := Context.generalize 4 hv hpoint
  exact Context.conjunctionIntro hm0 (Context.conjunctionIntro he hwhole)

/-- A forward-bijection clause onto a suffix is also a forward clause onto
its whole when graph edges from the common source are clean and suffix membership
implies whole membership. The proof does not infer either premise or any graph existence. -/
def suffix_forward_upgrade : KDerivation (imp suffixForward.encode
    (imp contained.encode (imp graphClean.encode firstClause.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [graphClean.encode,contained.encode,suffixForward.encode]
  have hc : Context Γ graphClean.encode := .head _ _
  have hs : Context Γ contained.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ suffixForward.encode := .hypothesis (by simp [Γ])
  have hpoint : Context Γ firstClauseBody.encode := by
    apply Context.deduction
    let Δ := [member 1 2,graphClean.encode,contained.encode,suffixForward.encode]
    have hm : Context Δ (member 1 2) := .head _ _
    have hclause : Context Δ suffixForwardBody.encode :=
      .mp (.under hf _) (.closed (allSpecialize 2 suffixForwardBody (by decide)))
    have hex : Context Δ (existsCode 3 suffixImage.encode) := .mp hm hclause
    have hlocal : Context Δ (imp suffixImage.encode firstTemplate.encode) :=
      .mp hm (.mp (.under hc _) (.mp (.under hs _) (.closed upgrade_image)))
    have hv3 : ∀ h, h ∈ Δ → KDerivation (imp h (allCode 3 h)) := by
      intro h hh
      simp only [Δ, List.mem_cons, List.not_mem_nil, or_false] at hh
      by_cases hM : h = member 1 2
      · subst h; exact (Formula.member 1 2).vacuity 3 (by decide)
      · have hr := hh.resolve_left hM
        by_cases hC : h = graphClean.encode
        · subst h; exact free_vacuity 3 graphClean (by decide)
        · have hr := hr.resolve_left hC
          by_cases hS : h = contained.encode
          · subst h; exact free_vacuity 3 contained (by decide)
          · have hF : h = suffixForward.encode := hr.resolve_left hS
            subst h; exact free_vacuity 3 suffixForward (by decide)
    have hall := Context.generalize 3 hv3 hlocal
    exact exists_map_context hall hex
  have hv2 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 2 h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases hC : h = graphClean.encode
    · subst h; exact free_vacuity 2 graphClean (by decide)
    · have hr := hh.resolve_left hC
      by_cases hS : h = contained.encode
      · subst h; exact free_vacuity 2 contained (by decide)
      · have hF : h = suffixForward.encode := hr.resolve_left hS
        subst h; exact free_vacuity 2 suffixForward (by decide)
  have hall := Context.generalize 2 hv2 hpoint
  simpa only [firstClause, Formula.encode] using hall

theorem suffix_forward_upgrade_certificate : theoremCode (certificate suffix_forward_upgrade) =
    imp suffixForward.encode (imp contained.encode (imp graphClean.encode firstClause.encode)) :=
  certificate_correct suffix_forward_upgrade

end PASoundness.PAtoCompactSuffixGuardedForwardUpgrade

#print axioms PASoundness.PAtoCompactSuffixGuardedForwardUpgrade.suffixImage
#print axioms PASoundness.PAtoCompactSuffixGuardedForwardUpgrade.suffixForwardBody
#print axioms PASoundness.PAtoCompactSuffixGuardedForwardUpgrade.suffixForward
#print axioms PASoundness.PAtoCompactSuffixGuardedForwardUpgrade.contained
#print axioms PASoundness.PAtoCompactSuffixGuardedForwardUpgrade.graphClean
#print axioms PASoundness.PAtoCompactSuffixGuardedForwardUpgrade.upgrade_image
#print axioms PASoundness.PAtoCompactSuffixGuardedForwardUpgrade.suffix_forward_upgrade
#print axioms PASoundness.PAtoCompactSuffixGuardedForwardUpgrade.suffix_forward_upgrade_certificate
