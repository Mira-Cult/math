import PASoundness.PAtoCompactProductOutputReverseCoverage
import PASoundness.PAtoCompactProductOutputReverseGraphUnique

/-! Assemble reverse existence and coordinate uniqueness for the same
supplied graph and the same selected factor pair. The source matrix, output
bijection, actual invariant and target membership remain explicit. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputReverseClause

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactProductOutputActualPoint PASoundness.PAtoCompactProductOutputCollectionInsideConditional
open PASoundness.PAtoCompactProductOutputReverseCoverage PASoundness.PAtoCompactProductOutputReverseGraphUnique

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def pointGuard : Formula := namedBoth assumptions (namedBoth actualInvariant (.member 42 33))
def rivalResult : Formula := namedBoth (.member 43 51) (namedBoth (.member 44 53) rivalTriple)
def uniqueness : Formula := .all 51 (.all 53 (.imp rivalResult
  (namedBoth (.equal 51 30) (.equal 53 31))))
def reverseWitness : Formula := namedBoth reverseResult uniqueness

/-- Add the coordinate uniqueness clause to the selected reverse witness. -/
def retain_reverse_witness : KDerivation (imp pointGuard.encode
    (imp reverseResult.encode reverseWitness.encode)) := by
  let Γ := [reverseResult.encode,pointGuard.encode]
  have hw : Context Γ reverseResult.encode := .head _ _
  have hg : Context Γ pointGuard.encode := .hypothesis (by simp [Γ])
  have hw' : Context Γ (both (member 43 30) (both (member 44 31) selectedTriple.encode)) := by
    simpa [reverseResult, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hw
  have hg' : Context Γ (both assumptions.encode (both actualInvariant.encode (member 42 33))) := by
    simpa [pointGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hg
  have hp : Context Γ (imp rivalResult.encode (both (equal 51 30) (equal 53 31))) := by
    apply Context.deduction
    let Δ := [rivalResult.encode,reverseResult.encode,pointGuard.encode]
    have hr : Context Δ rivalResult.encode := .head _ _
    have hr' : Context Δ (both (member 43 51) (both (member 44 53) rivalTriple.encode)) := by
      simpa [rivalResult, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hr
    have hguard : Context Δ graphGuard.encode := by
      simpa [graphGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
        Context.conjunctionIntro (.under (Context.conjunctionLeft hg') _)
          (Context.conjunctionIntro (.under (Context.conjunctionLeft (Context.conjunctionRight hg')) _)
            (Context.conjunctionIntro (.under (Context.conjunctionRight (Context.conjunctionRight hg')) _)
              (Context.conjunctionIntro (.under (Context.conjunctionLeft hw') _)
                (Context.conjunctionIntro (.under (Context.conjunctionLeft (Context.conjunctionRight hw')) _)
                  (Context.conjunctionIntro (Context.conjunctionLeft hr')
                    (Context.conjunctionIntro (Context.conjunctionLeft (Context.conjunctionRight hr'))
                      (Context.conjunctionIntro (.under (Context.conjunctionRight (Context.conjunctionRight hw')) _)
                        (Context.conjunctionRight (Context.conjunctionRight hr')))))))))
    exact .mp hguard (.closed reverse_graph_unique)
  have hv (v : Nat) (hW : v ∉ reverseResult.free) (hG : v ∉ pointGuard.free) :
      ∀ q, q ∈ Γ → KDerivation (imp q (allCode v q)) := by
    intro q hq
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
    by_cases he : q = reverseResult.encode
    · subst q; exact free_vacuity v reverseResult hW
    · have he' : q = pointGuard.encode := hq.resolve_left he
      subst q; exact free_vacuity v pointGuard hG
  have hu := Context.generalize 51 (hv 51 (by decide) (by decide))
    (Context.generalize 53 (hv 53 (by decide) (by decide)) hp)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  simpa [Γ, reverseWitness, uniqueness, namedBoth, CompactNamed.Formula.not,
    CompactNamed.Formula.encode, both, neg] using Context.conjunctionIntro hw hu

/-- Preserve the original ∃30∃31 reverse pair while adding its uniqueness. -/
def reverse_clause_point : KDerivation (imp assumptions.encode (imp actualInvariant.encode
    (imp (member 42 33) (existsCode 30 (existsCode 31 reverseWitness.encode))))) := by
  have h31 := conditionalExistsCongr 31 (free_vacuity 31 pointGuard (by decide)) retain_reverse_witness
  have h30 := conditionalExistsCongr 30 (free_vacuity 30 pointGuard (by decide)) h31
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 42 33,actualInvariant.encode,assumptions.encode]
  have hy : Context Γ (member 42 33) := .head _ _
  have hi : Context Γ actualInvariant.encode := .hypothesis (by simp [Γ])
  have ha : Context Γ assumptions.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ pointGuard.encode := by
    simpa [pointGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro ha (Context.conjunctionIntro hi hy)
  have he := Context.mp hy (Context.mp hi (Context.mp ha (.closed reverse_coverage)))
  exact .mp he (.mp hg (.closed h30))

theorem reverse_clause_point_certificate : theoremCode (certificate reverse_clause_point) =
    imp assumptions.encode (imp actualInvariant.encode (imp (member 42 33)
      (existsCode 30 (existsCode 31 reverseWitness.encode)))) := certificate_correct _

end PASoundness.PAtoCompactProductOutputReverseClause

#print axioms PASoundness.PAtoCompactProductOutputReverseClause.retain_reverse_witness
#print axioms PASoundness.PAtoCompactProductOutputReverseClause.reverse_clause_point
#print axioms PASoundness.PAtoCompactProductOutputReverseClause.reverse_clause_point_certificate
