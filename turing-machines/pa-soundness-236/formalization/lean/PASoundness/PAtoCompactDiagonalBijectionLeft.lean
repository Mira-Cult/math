import PASoundness.PAtoCompactDiagonalSoundInstance
import PASoundness.PAtoCompactAdjunction
import PASoundness.CompactFreshen
import PASoundness.CompactQuantifiers

/-! The first literal bijection clause for a supplied diagonal graph. Its
coverage, equal-input and edge-equality soundness hypotheses are explicit; no
graph existence, quotient reflexivity or PA interpretation is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalBijectionLeft
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactDiagonalSoundInstance
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Exact coverage clause of the candidate diagonal invariant. -/
def coverage : Nat := allCode 2 (imp (member 0 2) (graphFormula 6 2 2).encode)

def witnessBody : Formula := namedBoth (.member 1 3) (namedBoth (graphFormula 6 2 3)
  (.all 4 (.imp (namedBoth (.member 1 4) (graphFormula 6 2 4)) (.equal 4 3))))

def witnessAtTwo : Formula := namedBoth (.member 1 2) (namedBoth (graphFormula 6 2 2)
  (.all 4 (.imp (namedBoth (.member 1 4) (graphFormula 6 2 4)) (.equal 4 2))))

def leftFormula : Formula := .all 2 (.imp (.member 0 2) (.ex 3 witnessBody))

/-- Literal syntactic identity with the first conjunct of bijectionFormula. -/
theorem left_is_first : (match bijectionFormula with
  | .imp (.imp first _) _ => first
  | _ => .truth) = leftFormula := by rfl

/-- The coverage formula is vacuous at its own bound name 2, proved by
capture-safe alpha conversion rather than treating the name as absent. -/
def coverage_vacuity : KDerivation (imp coverage (allCode 2 coverage)) := by
  let f : Formula := .imp (.member 0 2) (graphFormula 6 2 2)
  let f' : Formula := .all 30 (replace 2 30 f)
  have ha := CompactNamed.universalAlpha 2 30 f (by decide) (by decide) (by decide)
  have hv : KDerivation (imp f'.encode (allCode 2 f'.encode)) := f'.vacuity 2 (by decide)
  exact compose ha.1 (compose hv (allCongr 2 ha.2))

/-- Under edge equality, every competing target has the same value as the
chosen diagonal target. This remains a conditional K proof. -/
def unique_target : KDerivation (imp equalSoundness.encode
    (allCode 4 (imp (both (member 1 4) (graphFormula 6 2 4).encode) (equal 4 2)))) := by
  let H := equalSoundness.encode
  let A := both (member 1 4) (graphFormula 6 2 4).encode
  have hv : KDerivation (imp H (allCode 4 H)) := equalSoundness.vacuity 4 (by decide)
  have hlocal : Context [H] (imp A (equal 4 2)) := by
    apply Context.deduction
    have hh : Context [A,H] H := .hypothesis (by simp)
    have ha : Context [A,H] A := Context.head _ _
    have hg : Context [A,H] (graphFormula 6 2 4).encode := Context.conjunctionRight ha
    exact Context.eqSymm (.mp hg (.mp hh (.closed instance_24)))
  apply Context.closeEmpty
  apply Context.deduction
  exact Context.generalize 4 (by
    intro z hz
    have he : z = H := by simpa using hz
    subst z
    exact hv) hlocal

/-- Supplied graph coverage and equal input sets yield the exact first
bijection clause, conditional on global edge-equality soundness. -/
def left_clause : KDerivation (imp equalSoundness.encode (imp coverage
    (imp (equal 0 1) leftFormula.encode))) := by
  let H := equalSoundness.encode
  let C := coverage
  let E := equal 0 1
  let M := member 0 2
  let Γ := [E,C,H]
  let Δ := [M,E,C,H]
  have hvH : KDerivation (imp H (allCode 2 H)) := equalSoundness.vacuity 2 (by decide)
  have hvE : KDerivation (imp E (allCode 2 E)) := equalityVacuity 0 1 2 (by decide) (by decide)
  have hcovBody : KDerivation (imp C (imp M (graphFormula 6 2 2).encode)) := by
    let f : Formula := .imp (.member 0 2) (graphFormula 6 2 2)
    exact CompactNamed.allSpecialize 2 f (by decide)
  have hex := exists_variable_intro 3 2 witnessBody (by decide) (by decide) (by decide)
  have hrepl : replace 3 2 witnessBody = witnessAtTwo := by decide
  rw [hrepl] at hex
  have hlocal : Context Γ (imp M (existsCode 3 witnessBody.encode)) := by
    apply Context.deduction
    have hm : Context Δ M := Context.head _ _
    have he : Context Δ E := .hypothesis (by simp [Δ])
    have hc : Context Δ C := .hypothesis (by simp [Δ])
    have hh : Context Δ H := .hypothesis (by simp [Δ])
    have hmem : Context Δ (member 1 2) := .mp hm (.mp he (.closed (memberLeftEquality 0 1 2)))
    have hgraph : Context Δ (graphFormula 6 2 2).encode := .mp hm (.mp hc (.closed hcovBody))
    have huniq : Context Δ (allCode 4
        (imp (both (member 1 4) (graphFormula 6 2 4).encode) (equal 4 2))) :=
      .mp hh (.closed unique_target)
    have hbody : Context Δ witnessAtTwo.encode :=
      Context.conjunctionIntro hmem (Context.conjunctionIntro hgraph huniq)
    exact .mp hbody (.closed hex)
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 2 h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases he : h = E
    · subst h; exact hvE
    · by_cases hc : h = C
      · subst h; exact coverage_vacuity
      · have ht : h = H := (hh.resolve_left he).resolve_left hc
        subst h; exact hvH
  have htarget : Context Γ leftFormula.encode := Context.generalize 2 hv hlocal
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact htarget

theorem left_clause_certificate : theoremCode (certificate left_clause) =
    imp equalSoundness.encode (imp coverage (imp (equal 0 1) leftFormula.encode)) :=
  certificate_correct left_clause

end PASoundness.PAtoCompactDiagonalBijectionLeft

#print axioms PASoundness.PAtoCompactDiagonalBijectionLeft.left_clause
#print axioms PASoundness.PAtoCompactDiagonalBijectionLeft.left_clause_certificate
