import PASoundness.PAtoCompactSuccCongruenceData
import PASoundness.PAtoCompactSuccessorInjective

/-! Literal K assembly of the first successor-bijection clause from two
explicit pointwise cases and a supplied premise vacuity derivation. This file
does not assert either pointwise case, any graph existence, or quotient
congruence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccBijectionLeft
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactSuccCongruenceData PASoundness.PAtoCompactSuccessorInjective
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The literal first bijection witness body for a source named 2. -/
def witnessBody : Formula := namedBoth (.member 8 3) (namedBoth (graphFormula 9 2 3)
  (.all 4 (.imp (namedBoth (.member 8 4) (graphFormula 9 2 4)) (.equal 4 3))))

def pointGoal : Nat := existsCode 3 witnessBody.encode

def leftFormula : Formula := .all 2 (.imp (.member 7 2) (.ex 3 witnessBody))

/-- This named formula is exactly the first conjunct of the substituted
bijection; no semantic equivalence is used. -/
theorem left_is_first : (match newBijection with
  | .imp (.imp first _) _ => first
  | _ => .truth) = leftFormula := by decide

/-- Given an explicit premise P, its vacuity at 2, its source-successor graph,
and both top and old-source pointwise K derivations, derive the exact left
clause. Each premise is a proof-data argument, not an assumed theorem. -/
def left_from_cases (P : Nat)
    (hVacuity : KDerivation (imp P (allCode 2 P)))
    (hSucc : KDerivation (imp P sourceSuccessor))
    (hOld : KDerivation (imp P (imp (member 0 2) pointGoal)))
    (hTop : KDerivation (imp P (imp (equal 2 0) pointGoal))) :
    KDerivation (imp P leftFormula.encode) := by
  let M := member 7 2
  have hlocal : Context [P] (imp M pointGoal) := by
    apply Context.deduction
    let Γ := [M,P]
    have hp : Context Γ P := .hypothesis (by simp [Γ])
    have hm : Context Γ M := Context.head _ _
    have hs : Context Γ sourceSuccessor := .mp hp (.closed hSucc)
    have hc : Context Γ (either (equal 2 0) (member 0 2)) :=
      .mp hm (.mp hs (.closed (successor_inspect 0 7 14 2 (by decide) (by decide) (by decide))))
    apply Context.disjunctionElim hc
    · exact .mp (Context.head _ (equal 2 0))
        (.mp (Context.under hp _) (.closed hTop))
    · exact .mp (Context.head _ (member 0 2))
        (.mp (Context.under hp _) (.closed hOld))
  have hv : ∀ z, z ∈ [P] → KDerivation (imp z (allCode 2 z)) := by
    intro z hz
    have he : z = P := by simpa only [List.mem_singleton] using hz
    cases he
    exact hVacuity
  have hall : Context [P] (allCode 2 (imp M pointGoal)) := Context.generalize 2 hv hlocal
  apply Context.closeEmpty
  apply Context.deduction
  exact hall

theorem left_from_cases_certificate (P : Nat)
    (hVacuity : KDerivation (imp P (allCode 2 P)))
    (hSucc : KDerivation (imp P sourceSuccessor))
    (hOld : KDerivation (imp P (imp (member 0 2) pointGoal)))
    (hTop : KDerivation (imp P (imp (equal 2 0) pointGoal))) :
    theoremCode (certificate (left_from_cases P hVacuity hSucc hOld hTop)) =
      imp P leftFormula.encode := certificate_correct (left_from_cases P hVacuity hSucc hOld hTop)

end PASoundness.PAtoCompactSuccBijectionLeft

#print axioms PASoundness.PAtoCompactSuccBijectionLeft.left_from_cases
#print axioms PASoundness.PAtoCompactSuccBijectionLeft.left_from_cases_certificate
