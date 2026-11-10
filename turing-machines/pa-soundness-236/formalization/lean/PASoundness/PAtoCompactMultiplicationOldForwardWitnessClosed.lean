import PASoundness.PAtoCompactMultiplicationOldForwardUniqueClosed
import PASoundness.PAtoCompactMultiplicationOldEndpointLift
import PASoundness.PAtoCompactProductOldTriplePreserved
import PASoundness.PAtoCompactFreeVacuity

/-! A finite K old-coordinate forward-witness transfer. The original forward
clause, old input memberships, graph inclusion, no-garbage and clean-old
hypotheses, new-result candidate guard, and literal cut alternative are
explicit. This does not construct a graph, handle the top-coordinate case,
or prove multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationOldForwardWitnessClosed
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactFixedFirstCoverageBase PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactMultiplicationOldForwardSpecialize
open PASoundness.PAtoCompactMultiplicationOldForwardUniqueConditional
open PASoundness.PAtoCompactMultiplicationOldForwardUniqueClosed
open PASoundness.PAtoCompactMultiplicationCleanOldMemberOutput
open PASoundness.PAtoCompactMultiplicationOldEndpointLift
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Explicit old-graph inclusion and old-result cut alternative. -/
def oldPreserved64 : Formula := .all 9 (.imp (.member 10 9) (.member 64 9))
def cutAlternative : Formula := namedEither (.equal 32 45) (.member 45 32)

/-- Context retained when moving the existing output to the new graph/result. -/
def hypotheses : Formula := namedBoth oldPreserved64
  (namedBoth (domainAt 100 45) (namedBoth cutAlternative
    PAtoCompactMultiplicationOldForwardUniqueClosed.hypotheses))

/-- New-result membership, extended-graph triple and the new uniqueness clause
for the same output witness 5. -/
def newOutput : Formula := namedBoth (.member 45 5)
  (namedBoth (tripleAt 64 5) newUnique)

private theorem old_output_shape : oldOutput = namedBoth (.member 32 5)
    (namedBoth (tripleAt 10 5) oldUnique) := by rfl

private def body_transfer : KDerivation (imp hypotheses.encode (imp oldOutput.encode newOutput.encode)) := by
  have hp : KDerivation (imp oldPreserved64.encode
      (imp (tripleAt 10 5).encode (tripleAt 64 5).encode)) := by
    exact PAtoCompactProductOldTriplePreserved.triple_preserved
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldOutput.encode,hypotheses.encode]
  have ho : Context Γ (both (member 32 5) (both (tripleAt 10 5).encode oldUnique.encode)) := by
    have hh : Context Γ oldOutput.encode := .head _ _
    simpa [old_output_shape,namedBoth,Formula.not,Formula.encode,both,neg] using hh
  have hh : Context Γ hypotheses.encode := .hypothesis (by simp [Γ])
  have hparts : Context Γ (both oldPreserved64.encode (both (domainAt 100 45).encode
      (both (either (equal 32 45) (member 45 32))
        PAtoCompactMultiplicationOldForwardUniqueClosed.hypotheses.encode))) := by
    simpa [hypotheses,cutAlternative,namedBoth,namedEither,Formula.not,Formula.encode,both,neg,either] using hh
  have hg := Context.conjunctionLeft hparts
  have hr := Context.conjunctionRight hparts
  have hd := Context.conjunctionLeft hr
  have hc := Context.conjunctionLeft (Context.conjunctionRight hr)
  have hu := Context.conjunctionRight (Context.conjunctionRight hr)
  have hm45 : Context Γ (member 45 5) :=
    .mp (Context.conjunctionLeft ho) (.mp hc (.mp hd (.closed (old_result_member 5 (by decide)))))
  have ht64 : Context Γ (tripleAt 64 5).encode :=
    .mp (Context.conjunctionLeft (Context.conjunctionRight ho)) (.mp hg (.closed hp))
  have huniq : Context Γ newUnique.encode :=
    .mp (Context.conjunctionRight (Context.conjunctionRight ho)) (.mp hu (.closed unique_closed))
  have hout := Context.conjunctionIntro hm45 (Context.conjunctionIntro ht64 huniq)
  simpa [newOutput,namedBoth,Formula.not,Formula.encode,both,neg] using hout

/-- The same old output witness serves the new forward point clause. -/
def old_forward_witness : KDerivation (imp hypotheses.encode
    (imp oldForward.encode (imp (member 31 4) (existsCode 5 newOutput.encode)))) := by
  have hv : KDerivation (imp hypotheses.encode (allCode 5 hypotheses.encode)) :=
    free_vacuity 5 hypotheses (by decide)
  have hex := conditionalExistsCongr 5 hv body_transfer
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 31 4,oldForward.encode,hypotheses.encode]
  have hb : Context Γ (member 31 4) := .head _ _
  have hf : Context Γ oldForward.encode := .hypothesis (by simp [Γ])
  have hh : Context Γ hypotheses.encode := .hypothesis (by simp [Γ])
  have hparts : Context Γ (both oldPreserved64.encode (both (domainAt 100 45).encode
      (both (either (equal 32 45) (member 45 32))
        PAtoCompactMultiplicationOldForwardUniqueClosed.hypotheses.encode))) := by
    simpa [hypotheses,cutAlternative,namedBoth,namedEither,Formula.not,Formula.encode,both,neg,either] using hh
  have hu := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hparts))
  have hu' : Context Γ (both (member 30 3) (both (noGarbage 64).encode oldClean.encode)) := by
    simpa [PAtoCompactMultiplicationOldForwardUniqueClosed.hypotheses,namedBoth,Formula.not,
      Formula.encode,both,neg] using hu
  have ha : Context Γ (member 30 3) := Context.conjunctionLeft hu'
  have hold : Context Γ (existsCode 5 oldOutput.encode) :=
    .mp hb (.mp ha (.mp hf (.closed old_forward_at_point)))
  exact .mp hold (.mp hh (.closed hex))

theorem old_forward_witness_certificate : theoremCode (certificate old_forward_witness) =
    imp hypotheses.encode (imp oldForward.encode (imp (member 31 4) (existsCode 5 newOutput.encode))) :=
  certificate_correct old_forward_witness
end PASoundness.PAtoCompactMultiplicationOldForwardWitnessClosed
#print axioms PASoundness.PAtoCompactMultiplicationOldForwardWitnessClosed.old_forward_witness
#print axioms PASoundness.PAtoCompactMultiplicationOldForwardWitnessClosed.old_forward_witness_certificate
