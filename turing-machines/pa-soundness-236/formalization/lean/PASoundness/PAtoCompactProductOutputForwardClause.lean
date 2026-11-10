import PASoundness.PAtoCompactProductOutputForwardCoverage
import PASoundness.PAtoCompactProductOutputForwardUnique

/-! Assemble pointwise forward existence and uniqueness for the same graph
and the same selected target output. The source matrix, output bijection,
actual invariant and factor memberships remain explicit. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputForwardClause

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactProductOutputActualPoint PASoundness.PAtoCompactProductOutputForwardCoverage
open PASoundness.PAtoCompactProductOutputForwardUnique PASoundness.PAtoCompactProductOutputCollectionInsideConditional

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def rivalResult : Formula := namedBoth (.member 42 51) rivalTriple
def uniqueness : Formula := .all 51 (.imp rivalResult (.equal 51 33))
def forwardWitness : Formula := namedBoth forwardResult uniqueness

/-- Retain an existing target witness and attach its competitor uniqueness. -/
def retain_forward_witness : KDerivation (imp pointGuard.encode
    (imp forwardResult.encode forwardWitness.encode)) := by
  let Γ := [forwardResult.encode,pointGuard.encode]
  have hw : Context Γ forwardResult.encode := .head _ _
  have hg : Context Γ pointGuard.encode := .hypothesis (by simp [Γ])
  have hw' : Context Γ (both (member 42 33) selectedTriple.encode) := by
    simpa [forwardResult, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hw
  have hg' : Context Γ (both actualInvariant.encode (both (member 43 30) (member 44 31))) := by
    simpa [pointGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hg
  have hp : Context Γ (imp rivalResult.encode (equal 51 33)) := by
    apply Context.deduction
    let Δ := [rivalResult.encode,forwardResult.encode,pointGuard.encode]
    have hr : Context Δ rivalResult.encode := .head _ _
    have hr' : Context Δ (both (member 42 51) rivalTriple.encode) := by
      simpa [rivalResult, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hr
    have hfg : Context Δ forwardGuard.encode := by
      simpa [forwardGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
        Context.conjunctionIntro (.under (Context.conjunctionLeft hg') _)
          (Context.conjunctionIntro (.under (Context.conjunctionLeft (Context.conjunctionRight hg')) _)
            (Context.conjunctionIntro (.under (Context.conjunctionRight (Context.conjunctionRight hg')) _)
              (Context.conjunctionIntro (.under (Context.conjunctionLeft hw') _)
                (Context.conjunctionIntro (Context.conjunctionLeft hr')
                  (Context.conjunctionIntro (.under (Context.conjunctionRight hw') _) (Context.conjunctionRight hr'))))))
    exact .mp hfg (.closed forward_unique)
  have hv : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 51 q)) := by
    intro q hq
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
    by_cases he : q = forwardResult.encode
    · subst q; exact free_vacuity 51 forwardResult (by decide)
    · have he' : q = pointGuard.encode := hq.resolve_left he
      subst q; exact free_vacuity 51 pointGuard (by decide)
  have hu := Context.generalize 51 hv hp
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  simpa [Γ, forwardWitness, uniqueness, namedBoth, CompactNamed.Formula.not,
    CompactNamed.Formula.encode, both, neg] using Context.conjunctionIntro hw hu

/-- Construct a target output together with its uniqueness clause, preserving
the original existential witness. -/
def forward_clause_point : KDerivation (imp assumptions.encode (imp actualInvariant.encode
    (imp (member 43 30) (imp (member 44 31) (existsCode 33 forwardWitness.encode))))) := by
  have hmap := conditionalExistsCongr 33 (free_vacuity 33 pointGuard (by decide)) retain_forward_witness
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 44 31,member 43 30,actualInvariant.encode,assumptions.encode]
  have hy : Context Γ (member 44 31) := .head _ _
  have hx : Context Γ (member 43 30) := .hypothesis (by simp [Γ])
  have hi : Context Γ actualInvariant.encode := .hypothesis (by simp [Γ])
  have ha : Context Γ assumptions.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ pointGuard.encode := by
    simpa [pointGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro hi (Context.conjunctionIntro hx hy)
  have he := Context.mp hy (Context.mp hx (Context.mp hi (Context.mp ha (.closed forward_coverage))))
  exact .mp he (.mp hg (.closed hmap))

theorem forward_clause_point_certificate : theoremCode (certificate forward_clause_point) =
    imp assumptions.encode (imp actualInvariant.encode (imp (member 43 30) (imp (member 44 31)
      (existsCode 33 forwardWitness.encode)))) := certificate_correct _

end PASoundness.PAtoCompactProductOutputForwardClause

#print axioms PASoundness.PAtoCompactProductOutputForwardClause.retain_forward_witness
#print axioms PASoundness.PAtoCompactProductOutputForwardClause.forward_clause_point
#print axioms PASoundness.PAtoCompactProductOutputForwardClause.forward_clause_point_certificate
