import PASoundness.PAtoCompactPartialInverseCoverageCase
import PASoundness.PAtoCompactPartialInverseInstantiate
import PASoundness.CompactFreshen

/-! Quantified forward coverage for a supplied partial-inverse successor step.
Every graph, point, image and alias premise remains explicit. This proves no
backward/no-spurious direction, witness elimination, or induction. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseCoverageAll
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactPartialInverseBase PASoundness.PAtoCompactPartialInverseInstantiate
open PASoundness.PAtoCompactPartialInverseImageWitness PASoundness.PAtoCompactPartialInverseCoverageCase
open PASoundness.PAtoCompactPartialInverseOldEdge
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def conj (a b : Formula) : Formula := (a.imp b.not).not

def suppliedPremises : Formula :=
  conj (namedAdjoin 7 11 9 14) (conj (pairFormula 11 13 12)
    (conj (imageBody 12 13) (conj (.equal 12 8)
      (conj (namedSuccessor 8 10 15) partialInverse))))

def coverageFormula : Formula := .all 2 (.all 3
  (.imp (conj (.member 0 2) (.member 1 3))
    (.imp (conj (.member 10 2) (graphFormula 6 2 3)) (graphFormula 9 3 2))))

private theorem premises_names_lt : ∀ v ∈ suppliedPremises.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ suppliedPremises.names.sup id at hm
  have hb : suppliedPremises.names.sup id < 30 := by decide
  omega

def freshPremises := freshen suppliedPremises 30 premises_names_lt

def premises_vacuity (v : Nat) (fresh : v ∉ freshPremises.formula.names) :
    KDerivation (imp suppliedPremises.encode (allCode v suppliedPremises.encode)) :=
  compose freshPremises.equivalent.forward (compose (freshPremises.formula.vacuity v fresh)
    (allCongr v freshPremises.equivalent.backward))

theorem fresh_2 : 2 ∉ freshPremises.formula.names := by decide
theorem fresh_3 : 3 ∉ freshPremises.formula.names := by decide

/-- All source/target pairs satisfy forward coverage of the successor-prefix
partial inverse, under the explicit fixed premises. -/
def coverage_all : KDerivation (imp suppliedPremises.encode coverageFormula.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let H := suppliedPremises.encode
  let Γ := [H]
  let Y := both (member 0 2) (member 1 3)
  let R := both (member 10 2) E
  have hlocal : Context Γ (imp Y (imp R N)) := by
    apply Context.deduction
    apply Context.deduction
    let Δ := [R,Y,H]
    have hr : Context Δ R := Context.head _ _
    have hy : Context Δ Y := .hypothesis (by simp [Δ])
    have hh : Context Δ H := .hypothesis (by simp [Δ])
    have ha : Context Δ A := Context.conjunctionLeft hh
    have htail1 := Context.conjunctionRight hh
    have hp : Context Δ P := Context.conjunctionLeft htail1
    have htail2 := Context.conjunctionRight htail1
    have hw : Context Δ imageWitness := Context.conjunctionLeft htail2
    have htail3 := Context.conjunctionRight htail2
    have halias : Context Δ (equal 12 8) := Context.conjunctionLeft htail3
    have htail4 := Context.conjunctionRight htail3
    have hs : Context Δ S := Context.conjunctionLeft htail4
    have hold : Context Δ partialInverse.encode := Context.conjunctionRight htail4
    have hpoint : Context Δ pointFormula.encode := .mp hold (.closed partial_inverse_instance)
    rw [point_formula_code] at hpoint
    have hequiv : Context Δ (both (imp (graphFormula 7 3 2).encode oldPrefixRhs)
        (imp oldPrefixRhs (graphFormula 7 3 2).encode)) := .mp hy hpoint
    have hcov : Context Δ oldCoverage := Context.conjunctionRight hequiv
    have htarget : Context Δ (member 1 3) := Context.conjunctionRight hy
    have hsource : Context Δ (member 10 2) := Context.conjunctionLeft hr
    have hedge : Context Δ E := Context.conjunctionRight hr
    exact .mp hedge (.mp hsource (.mp htarget (.mp hs (.mp hcov (.mp halias
      (.mp hw (.mp hp (.mp ha (.closed coverage_case)))))))))
  have hv3 : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 3 q)) := by
    intro q hq
    have he : q = H := by simpa [Γ] using hq
    subst q
    exact premises_vacuity 3 fresh_3
  have hv2 : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 2 q)) := by
    intro q hq
    have he : q = H := by simpa [Γ] using hq
    subst q
    exact premises_vacuity 2 fresh_2
  exact Context.generalize 2 hv2 (Context.generalize 3 hv3 hlocal)

theorem coverage_all_certificate : theoremCode (certificate coverage_all) =
    imp suppliedPremises.encode coverageFormula.encode := certificate_correct coverage_all

end PASoundness.PAtoCompactPartialInverseCoverageAll

#print axioms PASoundness.PAtoCompactPartialInverseCoverageAll.coverage_all
#print axioms PASoundness.PAtoCompactPartialInverseCoverageAll.coverage_all_certificate
