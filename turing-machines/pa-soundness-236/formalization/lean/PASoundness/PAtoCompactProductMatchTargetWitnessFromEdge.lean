import PASoundness.PAtoCompactProductMatchTargetOutput
import PASoundness.PAtoCompactSuccGraphOutputLift

/-! Reconstruct the target product's forward witness at a displayed target
edge. This aligns a target selected by the reverse product clause with the
forward-witness form of the matching-path relation; it does not prove the
complete reverse matching theorem. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchTargetWitnessFromEdge

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactSuccGraphOutputLift
open PASoundness.PAtoCompactProductMatchTargetOutput

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def target55 : Formula := replace 35 55 targetOutputBody
def target50 : Formula := replace 35 50 targetOutputBody
def unique50 : Formula := .imp (namedBoth (.member 44 9) (targetTriple 33 34 9)) (.equal 9 50)
def edgeGuard : Formula := namedBoth targetMatrix (namedBoth (.member 42 33)
  (namedBoth (.member 43 34) (namedBoth (.member 44 55) (targetTriple 33 34 55))))

theorem target50_shape : target50 = namedBoth (.member 44 50)
    (namedBoth (targetTriple 33 34 50) (.all 9 unique50)) := by decide

/-- From the target matrix and a displayed guarded triple, obtain its full
forward witness with uniqueness for that very output. -/
def target_witness : KDerivation (imp targetMatrix.encode (imp (member 42 33)
    (imp (member 43 34) (imp (member 44 55) (imp (targetTriple 33 34 55).encode target55.encode))))) := by
  have hi := universalInstance 9 55 unique50 (by decide) (by decide) (by decide)
  have hs : replace 9 55 unique50 =
      .imp (namedBoth (.member 44 55) (targetTriple 33 34 55)) (.equal 55 50) := by decide
  rw [hs] at hi
  have he := (equalityReplace 50 55 target50 (by decide) (by decide)).1
  have heshape : replace 50 55 target50 = target55 := by decide
  rw [heshape] at he
  have hpoint : KDerivation (imp edgeGuard.encode (imp target50.encode target55.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [target50.encode,edgeGuard.encode]
    have hw : Context Γ target50.encode := .head _ _
    have hg : Context Γ edgeGuard.encode := .hypothesis (by simp [Γ])
    have hw' : Context Γ (both (member 44 50)
        (both (targetTriple 33 34 50).encode (allCode 9 unique50.encode))) := by
      simpa [target50_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hw
    have hg' : Context Γ (both targetMatrix.encode (both (member 42 33)
        (both (member 43 34) (both (member 44 55) (targetTriple 33 34 55).encode)))) := by
      simpa [edgeGuard, namedBoth, Formula.not, Formula.encode, both, neg] using hg
    have hc := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg'))
    have hu := Context.conjunctionRight (Context.conjunctionRight hw')
    have heq : Context Γ (equal 55 50) := by
      have h := Context.mp hc (Context.mp hu (.closed hi))
      simpa [namedBoth, Formula.not, Formula.encode, both, neg] using h
    exact .mp hw (.mp (Context.eqSymm heq) (.closed he))
  have hv := edgeGuard.vacuity 50 (by decide)
  have hq := target55.vacuity 50 (by decide)
  have helim := guarded_exists_left 50 edgeGuard.encode target50.encode target55.encode hv hq hpoint
  have ha := (existentialAlpha 35 50 targetOutputBody (by decide) (by decide) (by decide)).1
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(targetTriple 33 34 55).encode,member 44 55,member 43 34,
    member 42 33,targetMatrix.encode]
  have he : Context Γ (targetTriple 33 34 55).encode := .head _ _
  have hz : Context Γ (member 44 55) := .hypothesis (by simp [Γ])
  have hy : Context Γ (member 43 34) := .hypothesis (by simp [Γ])
  have hx : Context Γ (member 42 33) := .hypothesis (by simp [Γ])
  have hm : Context Γ targetMatrix.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ edgeGuard.encode := by
    have h := Context.conjunctionIntro hm (Context.conjunctionIntro hx
      (Context.conjunctionIntro hy (Context.conjunctionIntro hz he)))
    simpa [edgeGuard, namedBoth, Formula.not, Formula.encode, both, neg] using h
  have hw : Context Γ (existsCode 35 targetOutputBody.encode) :=
    .mp hy (.mp hx (.mp hm (.closed target_output)))
  have hw' : Context Γ (existsCode 50 target50.encode) := by
    simpa [target50] using Context.mp hw (.closed ha)
  exact .mp hw' (.mp hg (.closed helim))

theorem target_witness_certificate : theoremCode (certificate target_witness) =
    imp targetMatrix.encode (imp (member 42 33) (imp (member 43 34)
      (imp (member 44 55) (imp (targetTriple 33 34 55).encode target55.encode)))) := certificate_correct _

end PASoundness.PAtoCompactProductMatchTargetWitnessFromEdge

#print axioms PASoundness.PAtoCompactProductMatchTargetWitnessFromEdge.target_witness
#print axioms PASoundness.PAtoCompactProductMatchTargetWitnessFromEdge.target_witness_certificate
