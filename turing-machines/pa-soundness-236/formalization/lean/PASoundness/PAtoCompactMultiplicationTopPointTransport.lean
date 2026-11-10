import PASoundness.PAtoCompactMultiplicationTopForwardPoint
import PASoundness.PAtoCompactMultiplicationForwardQuantGeneric
import PASoundness.PAtoCompactFreeVacuity

/-! Capture-safe transport of the checked top-major multiplication forward
point from fixed major30/minor3 to queried major3/minor4. The retained graph,
cleanliness, filter and row-coverage hypotheses remain explicit. This is not
a product matrix, graph existence, or multiplication totality theorem. -/
namespace PASoundness.PAtoCompactMultiplicationTopPointTransport
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactProductOldSuffixExclusion
open PASoundness.PAtoCompactMultiplicationTopCoverageWitness
open PASoundness.PAtoCompactMultiplicationCleanMapUnique41
open PASoundness.PAtoCompactMultiplicationTopUniqueConditional
open PASoundness.PAtoCompactMultiplicationTopForwardPoint
open PASoundness.PAtoCompactMultiplicationForwardQuantGeneric
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Point-independent conditions of the checked top-row proof. -/
def base : Formula := namedBoth oldClean
  (namedBoth (replace 0 31 (noGarbage 64))
    (namedBoth witnessContext (namedBoth mapBijection40 (replace 0 31 (coverage 64)))))

private def topWitness : Formula := .ex 5 (namedBoth (.member 45 5)
  (namedBoth PASoundness.PAtoCompactMultiplicationTopCoverageTriple.topTriple topUnique))
private def pointBody : Formula := .imp (.member 31 3) topWitness
private def minorWitness : Formula := replace 3 4 topWitness

private theorem top_witness_shape : topWitness.encode = existsCode 5
    (both (member 45 5) (both PASoundness.PAtoCompactMultiplicationTopCoverageTriple.topTriple.encode
      topUnique.encode)) := by rfl
private theorem minor_shape : replace 3 4 pointBody = .imp (.member 31 4) minorWitness := by decide
private theorem major_shape : replace 30 3 minorWitness = witness := by decide

/-- Generalize only the actual queried minor point, leaving the large base
context fixed using syntactic free-name vacuity. -/
private def all_minor : KDerivation (imp base.encode (allCode 3 pointBody.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [base.encode]
  have hb : Context Γ base.encode := .head _ _
  have hp : Context Γ pointBody.encode := by
    apply Context.deduction
    let Δ := [member 31 3,base.encode]
    have hm : Context Δ (member 31 3) := .head _ _
    have hbase : Context Δ base.encode := .hypothesis (by simp [Δ])
    have hs : Context Δ (both oldClean.encode
        (both (replace 0 31 (noGarbage 64)).encode
          (both witnessContext.encode (both mapBijection40.encode (replace 0 31 (coverage 64)).encode)))) := by
      simpa [base,namedBoth,Formula.not,Formula.encode,both,neg] using hbase
    have hPrem : Context Δ premises.encode := by
      have hp' := Context.conjunctionIntro (Context.conjunctionLeft hs)
        (Context.conjunctionIntro (Context.conjunctionLeft (Context.conjunctionRight hs))
          (Context.conjunctionIntro (Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hs)))
            (Context.conjunctionIntro
              (Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hs))))
              (Context.conjunctionIntro hm (Context.conjunctionRight (Context.conjunctionRight
                (Context.conjunctionRight (Context.conjunctionRight hs))))))))
      simpa [premises,namedBoth,Formula.not,Formula.encode,both,neg] using hp'
    have hw := Context.mp hPrem (.closed top_forward_point)
    simpa [pointBody,Formula.encode,top_witness_shape] using hw
  have hv : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 3 q)) := by
    intro q hq
    have he : q = base.encode := by simpa [Γ] using hq
    subst q
    exact free_vacuity 3 base (by decide)
  exact Context.generalize 3 hv hp

/-- A target major coordinate equal to 30, and a target minor in 31, have the
exact forward witness at queried labels 3,4. Existential output 5 is preserved
through equality transport. -/
def top_point_at4 : KDerivation (imp base.encode (imp (equal 3 30)
    (imp (member 31 4) witness.encode))) := by
  have hi := universalInstance 3 4 pointBody (by decide) (by decide) (by decide)
  rw [minor_shape] at hi
  have heq := (equalityReplace 30 3 minorWitness (by decide) (by decide)).1
  rw [major_shape] at heq
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 31 4,equal 3 30,base.encode]
  have hm : Context Γ (member 31 4) := .head _ _
  have he : Context Γ (equal 3 30) := .hypothesis (by simp [Γ])
  have hb : Context Γ base.encode := .hypothesis (by simp [Γ])
  have hall : Context Γ (allCode 3 pointBody.encode) := .mp hb (.closed all_minor)
  have hp : Context Γ (imp (member 31 4) minorWitness.encode) := by
    simpa [Formula.encode] using (.mp hall (.closed hi))
  have hw : Context Γ minorWitness.encode := .mp hm hp
  have he' : Context Γ (equal 30 3) := .mp he (.closed (equalitySymmetry 3 30))
  exact .mp hw (.mp he' (.closed heq))

theorem top_point_at4_certificate : theoremCode (certificate top_point_at4) =
    imp base.encode (imp (equal 3 30) (imp (member 31 4) witness.encode)) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationTopPointTransport
#print axioms PASoundness.PAtoCompactMultiplicationTopPointTransport.top_point_at4
#print axioms PASoundness.PAtoCompactMultiplicationTopPointTransport.top_point_at4_certificate
