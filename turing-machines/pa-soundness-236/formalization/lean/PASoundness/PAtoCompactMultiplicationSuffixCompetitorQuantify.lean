import PASoundness.PAtoCompactMultiplicationSuffixReverseExistence
import PASoundness.PAtoCompactFreeVacuity

/-! Conditional quantification of a pointwise K competitor-reflection proof
for the suffix case of the multiplication successor. The retained primary
witness includes its actual suffix-map edge. The ambient context and pointwise
proof remain explicit inputs; this does not prove reflection, product reverse
uniqueness, multiplication totality, or PA proof transport. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationSuffixCompetitorQuantify
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactMultiplicationSuffixReverseExistence
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The chosen product preimage and its retained edge in the same suffix map. -/
def primary : Formula := namedBoth (reversePreimageBody 3 4) (graphFormula 6 4 5)

/-- A competing, source-guarded product edge to the same output. -/
def competitor : Formula := reversePreimageBody 7 8

/-- Both product coordinates of a competitor agree with the chosen ones. -/
def equalities : Formula := namedBoth (.equal 7 3) (.equal 8 4)

/-- The exact competitor quantification required by the product reverse clause. -/
def uniqueBody : Formula := .all 7 (.all 8 (.imp competitor equalities))

/-- The pointwise implication remains an explicit K-proof input. -/
def pointCode (H : Formula) : Nat := imp H.encode (imp primary.encode
  (imp competitor.encode equalities.encode))

/-- Quantify a supplied pointwise competitor-reflection proof. H is an
arbitrary named context whose free names exclude the competitor labels. It
can retain the necessary graph cleanliness and suffix-filter assumptions. -/
def quantify (H : Formula) (h7 : 7 ∉ H.free) (h8 : 8 ∉ H.free)
    (hpoint : KDerivation (pointCode H)) :
    KDerivation (imp H.encode (imp primary.encode uniqueBody.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [primary.encode, H.encode]
  have hp : Context Γ primary.encode := .head _ _
  have hh : Context Γ H.encode := .hypothesis (by simp [Γ])
  have hl : Context Γ (imp competitor.encode equalities.encode) :=
    .mp hp (.mp hh (.closed hpoint))
  have hv8 : ∀ a, a ∈ Γ → KDerivation (imp a (allCode 8 a)) := by
    intro a ha
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at ha
    by_cases he : a = primary.encode
    · subst a; exact free_vacuity 8 primary (by decide)
    · have he' : a = H.encode := ha.resolve_left he
      subst a; exact free_vacuity 8 H h8
  have hv7 : ∀ a, a ∈ Γ → KDerivation (imp a (allCode 7 a)) := by
    intro a ha
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at ha
    by_cases he : a = primary.encode
    · subst a; exact free_vacuity 7 primary (by decide)
    · have he' : a = H.encode := ha.resolve_left he
      subst a; exact free_vacuity 7 H h7
  have hall8 := Context.generalize 8 hv8 hl
  have hall7 := Context.generalize 7 hv7 hall8
  change Context Γ (allCode 7 (allCode 8 (imp competitor.encode equalities.encode)))
  exact hall7

theorem quantify_certificate (H : Formula) (h7 : 7 ∉ H.free) (h8 : 8 ∉ H.free)
    (hpoint : KDerivation (pointCode H)) :
    theoremCode (certificate (quantify H h7 h8 hpoint)) =
      imp H.encode (imp primary.encode uniqueBody.encode) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationSuffixCompetitorQuantify
#print axioms PASoundness.PAtoCompactMultiplicationSuffixCompetitorQuantify.quantify
#print axioms PASoundness.PAtoCompactMultiplicationSuffixCompetitorQuantify.quantify_certificate
