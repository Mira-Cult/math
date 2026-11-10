import PASoundness.PAtoCompactMultiplicationCandidate
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.CompactQuantifiers

/-! Conditional K transfer of the old-output reverse uniqueness clause to
an extended graph. The explicit competitor reflection must supply BOTH old
source membership and the old triple. This does not prove that reflection,
construct a graph, or establish multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOldReverseUniqueTransfer
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFreeVacuity
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- A product triple using the indicated graph and competitor labels 7,8,5. -/
def competitorTriple (g : Nat) : Formula := .ex 18
  (namedBoth (pairFormula 18 7 8) (graphFormula g 18 5))
private def equalities : Formula := namedBoth (.equal 7 3) (.equal 8 4)
private def oldBody : Formula := .imp
  (namedBoth (.member 30 7) (namedBoth (.member 31 8) (competitorTriple 10))) equalities
private def newBody : Formula := .imp
  (namedBoth (.member 38 7) (namedBoth (.member 31 8) (competitorTriple 64))) equalities
/-- Uniqueness against competitors in the old graph and old source. -/
def oldUnique : Formula := .all 7 (.all 8 oldBody)
/-- Uniqueness against competitors in the extended graph and new source. -/
def newUnique : Formula := .all 7 (.all 8 newBody)

/-- Under a retained guard, a finite K reflection that supplies old source
membership and the old triple transfers old-output input uniqueness. The guard
must be vacuous at the quantified competitor labels 7 and 8. -/
def unique_from_reflection (G : Formula)
    (hG7 : KDerivation (imp G.encode (allCode 7 G.encode)))
    (hG8 : KDerivation (imp G.encode (allCode 8 G.encode)))
    (reflect : KDerivation (imp G.encode (imp (member 38 7) (imp (member 31 8)
      (imp (competitorTriple 64).encode
        (both (member 30 7) (competitorTriple 10).encode)))))) :
    KDerivation (imp G.encode (imp oldUnique.encode newUnique.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldUnique.encode,G.encode]
  have ho : Context Γ oldUnique.encode := .head _ _
  have hg : Context Γ G.encode := .hypothesis (by simp [Γ])
  have h7 := allSpecialize 7 (.all 8 oldBody) (by decide)
  have h8 := allSpecialize 8 oldBody (by decide)
  have hOldAt : Context Γ oldBody.encode :=
    .mp (.mp ho (.closed h7)) (.closed h8)
  have point : Context Γ newBody.encode := by
    change Context Γ (imp (namedBoth (.member 38 7) (namedBoth (.member 31 8) (competitorTriple 64))).encode equalities.encode)
    apply Context.deduction
    let Δ := [(namedBoth (.member 38 7) (namedBoth (.member 31 8) (competitorTriple 64))).encode,
      oldUnique.encode,G.encode]
    have hc : Context Δ (both (member 38 7) (both (member 31 8) (competitorTriple 64).encode)) := by
      have hraw : Context Δ (namedBoth (.member 38 7) (namedBoth (.member 31 8) (competitorTriple 64))).encode := .head _ _
      change Context Δ (both (member 38 7) (both (member 31 8) (competitorTriple 64).encode)) at hraw
      exact hraw
    have hmajor := Context.conjunctionLeft hc
    have hminor := Context.conjunctionLeft (Context.conjunctionRight hc)
    have htriple := Context.conjunctionRight (Context.conjunctionRight hc)
    have href : Context Δ (both (member 30 7) (competitorTriple 10).encode) :=
      .mp htriple (.mp hminor (.mp hmajor (.mp (.under hg _) (.closed reflect))))
    have hold : Context Δ (namedBoth (.member 30 7)
        (namedBoth (.member 31 8) (competitorTriple 10))).encode := by
      simpa [namedBoth,Formula.encode,Formula.not,both,neg] using
        Context.conjunctionIntro (Context.conjunctionLeft href)
          (Context.conjunctionIntro hminor (Context.conjunctionRight href))
    exact .mp hold (.under hOldAt _)
  have ho7 : KDerivation (imp oldUnique.encode (allCode 7 oldUnique.encode)) :=
    free_vacuity 7 oldUnique (by decide)
  have ho8 : KDerivation (imp oldUnique.encode (allCode 8 oldUnique.encode)) :=
    free_vacuity 8 oldUnique (by decide)
  have hv7 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 7 h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases he : h = oldUnique.encode
    · subst h; exact ho7
    · have he2 : h = G.encode := hh.resolve_left he
      subst h; exact hG7
  have hv8 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 8 h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases he : h = oldUnique.encode
    · subst h; exact ho8
    · have he2 : h = G.encode := hh.resolve_left he
      subst h; exact hG8
  have hall8 := Context.generalize 8 hv8 point
  have hall7 := Context.generalize 7 hv7 hall8
  exact hall7

theorem unique_from_reflection_certificate (G : Formula)
    (hG7 : KDerivation (imp G.encode (allCode 7 G.encode)))
    (hG8 : KDerivation (imp G.encode (allCode 8 G.encode)))
    (reflect : KDerivation (imp G.encode (imp (member 38 7) (imp (member 31 8)
      (imp (competitorTriple 64).encode
        (both (member 30 7) (competitorTriple 10).encode)))))) :
    theoremCode (certificate (unique_from_reflection G hG7 hG8 reflect)) =
      imp G.encode (imp oldUnique.encode newUnique.encode) :=
  certificate_correct (unique_from_reflection G hG7 hG8 reflect)
end PASoundness.PAtoCompactProductOldReverseUniqueTransfer
#print axioms PASoundness.PAtoCompactProductOldReverseUniqueTransfer.unique_from_reflection
#print axioms PASoundness.PAtoCompactProductOldReverseUniqueTransfer.unique_from_reflection_certificate
