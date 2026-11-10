import PASoundness.PAtoCompactProductMatchReverseGraphAll
import PASoundness.PAtoCompactProductMatchGraphReverseUnique
import PASoundness.PAtoCompactFreeVacuity

/-! Combine guarded reverse coverage and uniqueness into an explicit
preimage-witness clause with the same selected source throughout. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchReverseBijectionClause

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactProductMatchReverseGraphCoverage
open PASoundness.PAtoCompactProductMatchReverseGraphAll PASoundness.PAtoCompactProductMatchGraphReverseUnique

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def preimageTest : Formula := namedBoth (.member 2 52) (graphFormula 58 52 55)
def preimageUnique : Formula := .all 52 (.imp preimageTest (.equal 52 32))
def preimageWitness : Formula := namedBoth (.member 2 32)
  (namedBoth (graphFormula 58 32 55) preimageUnique)
def reverseClause : Formula := .all 55 (.imp (.member 44 55) (.ex 32 preimageWitness))
def pointGuard : Formula := namedBoth reverseUniqueAll (.member 44 55)

def witness_from_unique : KDerivation (imp pointGuard.encode
    (imp graphResult.encode preimageWitness.encode)) := by
  let Q : Formula := .imp endpointGuard (.equal 32 52)
  have h32 := allSpecialize 32 (.all 52 (.all 55 Q)) (by decide)
  have h52 := allSpecialize 52 (.all 55 Q) (by decide)
  have h55 := allSpecialize 55 Q (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [graphResult.encode,pointGuard.encode]
  have hw : Context Γ graphResult.encode := .head _ _
  have hw' : Context Γ (both (member 2 32) (graphFormula 58 32 55).encode) := by
    simpa [graphResult, namedBoth, Formula.not, Formula.encode, both, neg] using hw
  have hlocal : Context Γ (imp preimageTest.encode (equal 52 32)) := by
    apply Context.deduction
    let Δ := [preimageTest.encode,graphResult.encode,pointGuard.encode]
    have ht : Context Δ preimageTest.encode := .head _ _
    have hwΔ : Context Δ graphResult.encode := .hypothesis (by simp [Δ])
    have hgΔ : Context Δ pointGuard.encode := .hypothesis (by simp [Δ])
    have ht' : Context Δ (both (member 2 52) (graphFormula 58 52 55).encode) := by
      simpa [preimageTest, namedBoth, Formula.not, Formula.encode, both, neg] using ht
    have hwΔ' : Context Δ (both (member 2 32) (graphFormula 58 32 55).encode) := by
      simpa [graphResult, namedBoth, Formula.not, Formula.encode, both, neg] using hwΔ
    have hgΔ' : Context Δ (both reverseUniqueAll.encode (member 44 55)) := by
      simpa [pointGuard, namedBoth, Formula.not, Formula.encode, both, neg] using hgΔ
    have he : Context Δ endpointGuard.encode := by
      have h := Context.conjunctionIntro (Context.conjunctionLeft hwΔ')
        (Context.conjunctionIntro (Context.conjunctionLeft ht')
          (Context.conjunctionIntro (Context.conjunctionRight hgΔ')
            (Context.conjunctionIntro (Context.conjunctionRight hwΔ') (Context.conjunctionRight ht'))))
      simpa [endpointGuard, namedBoth, Formula.not, Formula.encode, both, neg] using h
    have hu : Context Δ (imp endpointGuard.encode (equal 32 52)) := by
      have h := Context.mp (Context.mp (Context.mp (Context.conjunctionLeft hgΔ') (.closed h32)) (.closed h52)) (.closed h55)
      simpa [reverseUniqueAll, outputPoint, Q, Formula.encode] using h
    simpa [Δ] using Context.eqSymm (Context.mp he hu)
  have hv : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 52 q)) := by
    intro q hq
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
    by_cases he : q = graphResult.encode
    · subst q; exact graphResult.vacuity 52 (by decide)
    · have he' : q = pointGuard.encode := hq.resolve_left he
      subst q; exact free_vacuity 52 pointGuard (by decide)
  have hu := Context.generalize 52 hv hlocal
  have h := Context.conjunctionIntro (Context.conjunctionLeft hw')
    (Context.conjunctionIntro (Context.conjunctionRight hw') hu)
  simpa [Γ, preimageWitness, preimageUnique, preimageTest, namedBoth, Formula.not, Formula.encode, both, neg] using h

def coverage_unique_to_reverse : KDerivation (imp reverseUniqueAll.encode
    (imp reverseCoverage.encode reverseClause.encode)) := by
  have hmap := conditionalExistsCongr 32 (free_vacuity 32 pointGuard (by decide)) witness_from_unique
  let B : Formula := .imp (.member 44 55) (.ex 32 graphResult)
  have hspec := allSpecialize 55 B (by decide)
  let Γ := [reverseCoverage.encode,reverseUniqueAll.encode]
  have hlocal : Context Γ (imp (member 44 55) (existsCode 32 preimageWitness.encode)) := by
    apply Context.deduction
    let Δ := [member 44 55,reverseCoverage.encode,reverseUniqueAll.encode]
    have hx : Context Δ (member 44 55) := .head _ _
    have hc : Context Δ reverseCoverage.encode := .hypothesis (by simp [Δ])
    have hu : Context Δ reverseUniqueAll.encode := .hypothesis (by simp [Δ])
    have hc' : Context Δ (imp (member 44 55) (existsCode 32 graphResult.encode)) := by
      have h := Context.mp hc (.closed hspec)
      simpa [reverseCoverage, B, Formula.encode] using h
    have hg : Context Δ pointGuard.encode := by
      simpa [pointGuard, namedBoth, Formula.not, Formula.encode, both, neg] using Context.conjunctionIntro hu hx
    simpa [Δ] using Context.mp (Context.mp hx hc') (Context.mp hg (.closed hmap))
  have hv : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 55 q)) := by
    intro q hq
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
    by_cases he : q = reverseCoverage.encode
    · subst q; exact free_vacuity 55 reverseCoverage (by decide)
    · have he' : q = reverseUniqueAll.encode := hq.resolve_left he
      subst q; exact free_vacuity 55 reverseUniqueAll (by decide)
  have hall := Context.generalize 55 hv hlocal
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  simpa [Γ, reverseClause, Formula.encode] using hall

theorem coverage_unique_to_reverse_certificate : theoremCode (certificate coverage_unique_to_reverse) =
    imp reverseUniqueAll.encode (imp reverseCoverage.encode reverseClause.encode) := certificate_correct _

end PASoundness.PAtoCompactProductMatchReverseBijectionClause

#print axioms PASoundness.PAtoCompactProductMatchReverseBijectionClause.witness_from_unique
#print axioms PASoundness.PAtoCompactProductMatchReverseBijectionClause.coverage_unique_to_reverse
#print axioms PASoundness.PAtoCompactProductMatchReverseBijectionClause.coverage_unique_to_reverse_certificate
