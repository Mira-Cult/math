import PASoundness.PAtoCompactProductMatchForwardGraphAll
import PASoundness.PAtoCompactProductMatchGraphForwardUniqueAll
import PASoundness.PAtoCompactFreeVacuity

/-! Combine guarded forward coverage and uniqueness into a single explicit
bijection witness clause, with the same target witness throughout. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchForwardBijectionClause

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactProductMatchForwardGraphCoverage
open PASoundness.PAtoCompactProductMatchForwardGraphAll PASoundness.PAtoCompactProductMatchGraphForwardUnique
open PASoundness.PAtoCompactProductMatchGraphForwardUniqueAll

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def imageTest : Formula := namedBoth (.member 44 55) (graphFormula 58 32 55)
def imageUnique : Formula := .all 55 (.imp imageTest (.equal 55 35))
def imageWitness : Formula := namedBoth (.member 44 35)
  (namedBoth (graphFormula 58 32 35) imageUnique)
def forwardClause : Formula := .all 32 (.imp (.member 2 32) (.ex 35 imageWitness))
def pointGuard : Formula := namedBoth forwardUniqueAll (.member 2 32)

def witness_from_unique : KDerivation (imp pointGuard.encode
    (imp forwardResult.encode imageWitness.encode)) := by
  let Q : Formula := .imp endpoints (.equal 55 35)
  have h32 := allSpecialize 32 (.all 35 (.all 55 Q)) (by decide)
  have h35 := allSpecialize 35 (.all 55 Q) (by decide)
  have h55 := allSpecialize 55 Q (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [forwardResult.encode,pointGuard.encode]
  have hw : Context Γ forwardResult.encode := .head _ _
  have hg : Context Γ pointGuard.encode := .hypothesis (by simp [Γ])
  have hw' : Context Γ (both (member 44 35) (graphFormula 58 32 35).encode) := by
    simpa [forwardResult, namedBoth, Formula.not, Formula.encode, both, neg] using hw
  have hg' : Context Γ (both forwardUniqueAll.encode (member 2 32)) := by
    simpa [pointGuard, namedBoth, Formula.not, Formula.encode, both, neg] using hg
  have hlocal : Context Γ (imp imageTest.encode (equal 55 35)) := by
    apply Context.deduction
    let Δ := [imageTest.encode,forwardResult.encode,pointGuard.encode]
    have ht : Context Δ imageTest.encode := .head _ _
    have hwΔ : Context Δ forwardResult.encode := .hypothesis (by simp [Δ])
    have hgΔ : Context Δ pointGuard.encode := .hypothesis (by simp [Δ])
    have ht' : Context Δ (both (member 44 55) (graphFormula 58 32 55).encode) := by
      simpa [imageTest, namedBoth, Formula.not, Formula.encode, both, neg] using ht
    have hwΔ' : Context Δ (both (member 44 35) (graphFormula 58 32 35).encode) := by
      simpa [forwardResult, namedBoth, Formula.not, Formula.encode, both, neg] using hwΔ
    have hgΔ' : Context Δ (both forwardUniqueAll.encode (member 2 32)) := by
      simpa [pointGuard, namedBoth, Formula.not, Formula.encode, both, neg] using hgΔ
    have he : Context Δ endpoints.encode := by
      have h := Context.conjunctionIntro (Context.conjunctionRight hgΔ')
        (Context.conjunctionIntro (Context.conjunctionLeft hwΔ')
          (Context.conjunctionIntro (Context.conjunctionLeft ht')
            (Context.conjunctionIntro (Context.conjunctionRight hwΔ') (Context.conjunctionRight ht'))))
      simpa [endpoints, namedBoth, Formula.not, Formula.encode, both, neg] using h
    have hu : Context Δ (imp endpoints.encode (equal 55 35)) := by
      have h := Context.mp (Context.mp (Context.mp (Context.conjunctionLeft hgΔ') (.closed h32)) (.closed h35)) (.closed h55)
      simpa [forwardUniqueAll, Q, Formula.encode] using h
    simpa [Δ] using Context.mp he hu
  have hv : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 55 q)) := by
    intro q hq
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
    by_cases he : q = forwardResult.encode
    · subst q; exact forwardResult.vacuity 55 (by decide)
    · have he' : q = pointGuard.encode := hq.resolve_left he
      subst q; exact free_vacuity 55 pointGuard (by decide)
  have hu := Context.generalize 55 hv hlocal
  have h := Context.conjunctionIntro (Context.conjunctionLeft hw')
    (Context.conjunctionIntro (Context.conjunctionRight hw') hu)
  simpa [Γ, imageWitness, imageUnique, imageTest, namedBoth, Formula.not, Formula.encode, both, neg] using h

def coverage_unique_to_forward : KDerivation (imp forwardUniqueAll.encode
    (imp forwardCoverage.encode forwardClause.encode)) := by
  have hmap := conditionalExistsCongr 35 (free_vacuity 35 pointGuard (by decide)) witness_from_unique
  let B : Formula := .imp (.member 2 32) (.ex 35 forwardResult)
  have hspec := allSpecialize 32 B (by decide)
  let Γ := [forwardCoverage.encode,forwardUniqueAll.encode]
  have hlocal : Context Γ (imp (member 2 32) (existsCode 35 imageWitness.encode)) := by
    apply Context.deduction
    let Δ := [member 2 32,forwardCoverage.encode,forwardUniqueAll.encode]
    have hx : Context Δ (member 2 32) := .head _ _
    have hc : Context Δ forwardCoverage.encode := .hypothesis (by simp [Δ])
    have hu : Context Δ forwardUniqueAll.encode := .hypothesis (by simp [Δ])
    have hc' : Context Δ (imp (member 2 32) (existsCode 35 forwardResult.encode)) := by
      have h := Context.mp hc (.closed hspec)
      simpa [forwardCoverage, B, Formula.encode] using h
    have hg : Context Δ pointGuard.encode := by
      simpa [pointGuard, namedBoth, Formula.not, Formula.encode, both, neg] using Context.conjunctionIntro hu hx
    simpa [Δ] using Context.mp (Context.mp hx hc') (Context.mp hg (.closed hmap))
  have hv : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 32 q)) := by
    intro q hq
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
    by_cases he : q = forwardCoverage.encode
    · subst q; exact free_vacuity 32 forwardCoverage (by decide)
    · have he' : q = forwardUniqueAll.encode := hq.resolve_left he
      subst q; exact free_vacuity 32 forwardUniqueAll (by decide)
  have hall := Context.generalize 32 hv hlocal
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  simpa [Γ, forwardClause, Formula.encode] using hall

theorem coverage_unique_to_forward_certificate : theoremCode (certificate coverage_unique_to_forward) =
    imp forwardUniqueAll.encode (imp forwardCoverage.encode forwardClause.encode) := certificate_correct _

end PASoundness.PAtoCompactProductMatchForwardBijectionClause

#print axioms PASoundness.PAtoCompactProductMatchForwardBijectionClause.witness_from_unique
#print axioms PASoundness.PAtoCompactProductMatchForwardBijectionClause.coverage_unique_to_forward
#print axioms PASoundness.PAtoCompactProductMatchForwardBijectionClause.coverage_unique_to_forward_certificate
