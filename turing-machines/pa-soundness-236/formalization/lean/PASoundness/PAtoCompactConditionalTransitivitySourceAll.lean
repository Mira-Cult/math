import PASoundness.PAtoCompactConditionalTransitivitySourceComposite
import PASoundness.CompactFreshen

/-! Quantified source uniqueness for an explicitly supplied restricted
composition graph. No graph construction or quotient transitivity is claimed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivitySourceAll
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactConditionalTransitivityPoint
open PASoundness.PAtoCompactConditionalTransitivitySecondUnique
open PASoundness.PAtoCompactConditionalTransitivitySourceComposite
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The two actual bijections and the explicitly supplied restricted
composition. The graph 9 is not required to have any behavior outside the
guarded source and target domains. -/
def background : Formula := namedBoth bijectionFormula (namedBoth secondBijection composition)

/-- Both candidate sources and the common target lie in their respective
domains and have the two displayed edges. -/
def guard : Formula := namedBoth (.member 8 3) (namedBoth (.member 0 2)
  (namedBoth (.member 0 4) (namedBoth edge secondEdge)))

def point : Formula := .imp guard (.equal 4 2)
def family : Formula := .all 3 (.all 2 (.all 4 point))

private theorem background_names_lt : ∀ v ∈ background.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ background.names.sup id at hm
  have hb : background.names.sup id < 30 := by decide
  omega

/-- Alpha-freshening is required because the original graph clauses reuse
names 2, 3, and 4 as binders. The equivalent freshened formula has none of
those names free or bound. -/
private def freshBackground := freshen background 30 background_names_lt
private theorem fresh_no2 : 2 ∉ freshBackground.formula.names := by decide
private theorem fresh_no3 : 3 ∉ freshBackground.formula.names := by decide
private theorem fresh_no4 : 4 ∉ freshBackground.formula.names := by decide
private def backgroundVacuity (v : Nat) (h : v ∉ freshBackground.formula.names) :
    KDerivation (imp background.encode (allCode v background.encode)) :=
  compose freshBackground.equivalent.forward
    (compose (freshBackground.formula.vacuity v h)
      (allCongr v freshBackground.equivalent.backward))

/-- The actual two bijections and guarded composition imply the quantified
preimage-uniqueness test at every guarded source/target triple. -/
def source_unique_all : KDerivation (imp background.encode family.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [background.encode]
  have hbackground : Context Γ background.encode := Context.head [] _
  have hpoint : Context Γ point.encode := by
    apply Context.deduction
    let Δ := guard.encode :: Γ
    have hg : Context Δ guard.encode := Context.head _ _
    have hb : Context Δ background.encode := Context.under hbackground _
    have hf : Context Δ bijectionFormula.encode := Context.conjunctionLeft hb
    have hb' := Context.conjunctionRight hb
    have hs : Context Δ secondBijection.encode := Context.conjunctionLeft hb'
    have hc : Context Δ composition.encode := Context.conjunctionRight hb'
    have hm : Context Δ (member 8 3) := Context.conjunctionLeft hg
    have ht := Context.conjunctionRight hg
    have ha : Context Δ (member 0 2) := Context.conjunctionLeft ht
    have ht := Context.conjunctionRight ht
    have ha' : Context Δ (member 0 4) := Context.conjunctionLeft ht
    have ht := Context.conjunctionRight ht
    have he : Context Δ edge.encode := Context.conjunctionLeft ht
    have he' : Context Δ secondEdge.encode := Context.conjunctionRight ht
    have hp : Context Δ PAtoCompactConditionalTransitivitySourceComposite.premises.encode :=
      Context.conjunctionIntro hf (Context.conjunctionIntro hs
        (Context.conjunctionIntro hc (Context.conjunctionIntro ha
          (Context.conjunctionIntro ha' (Context.conjunctionIntro hm
            (Context.conjunctionIntro he he'))))))
    have heq : Context Δ (equal 2 4) := .mp hp (.closed guarded_composite_source_unique)
    exact Context.eqSymm heq
  have hv (v : Nat) (hf : v ∉ freshBackground.formula.names) :
      ∀ h, h ∈ Γ → KDerivation (imp h (allCode v h)) := by
    intro h hh
    have he : h = background.encode := by simpa [Γ] using hh
    subst h
    exact backgroundVacuity v hf
  exact Context.generalize 3 (hv 3 fresh_no3)
    (Context.generalize 2 (hv 2 fresh_no2)
      (Context.generalize 4 (hv 4 fresh_no4) hpoint))

theorem source_unique_all_certificate : theoremCode (certificate source_unique_all) =
    imp background.encode family.encode := certificate_correct source_unique_all

end PASoundness.PAtoCompactConditionalTransitivitySourceAll

#print axioms PASoundness.PAtoCompactConditionalTransitivitySourceAll.source_unique_all
#print axioms PASoundness.PAtoCompactConditionalTransitivitySourceAll.source_unique_all_certificate
