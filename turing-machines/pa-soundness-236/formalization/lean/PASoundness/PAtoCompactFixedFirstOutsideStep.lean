import PASoundness.PAtoCompactFixedFirstPreservedBase
import PASoundness.PAtoCompactProductRowOutsideCoverage
import PASoundness.PAtoCompactFixedFirstOutsideNoGarbage

/-! The outside-domain successor branch of a fixed-first product row: the
same supplied graph retains old-graph preservation, coverage and no-garbage.
This is an actual finite K proof step, not full row collection or multiplication. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFixedFirstOutsideStep
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactFixedFirstCoverageBase PASoundness.PAtoCompactFixedFirstPreservedBase
open PASoundness.PAtoCompactProductRowOutsideCoverage PASoundness.PAtoCompactFixedFirstOutsideNoGarbage
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private def newInv : Formula := replace 0 1 (rowInvariantPreserved 7)
private theorem newInv_shape : newInv = namedBoth (oldPreserved 7)
    (namedBoth (replace 0 1 (coverage 7)) (replace 0 1 (noGarbage 7))) := by decide

/-- The same graph satisfies the strengthened invariant after an outside
prefix step. Every row edge is supplied existentially, not by assuming all
set-theoretic pair representatives belong to the graph. -/
def outside_step : KDerivation (imp (successorCode 0 1 2)
    (imp (neg (member 31 0))
      (imp (rowInvariantPreserved 7).encode (replace 0 1 (rowInvariantPreserved 7)).encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(rowInvariantPreserved 7).encode,neg (member 31 0),successorCode 0 1 2]
  have hi : Context Γ (rowInvariantPreserved 7).encode := .head _ _
  have hn : Context Γ (neg (member 31 0)) := .hypothesis (by simp [Γ])
  have hs : Context Γ (successorCode 0 1 2) := .hypothesis (by simp [Γ])
  have hparts : Context Γ (both (oldPreserved 7).encode
      (both (coverage 7).encode (noGarbage 7).encode)) := by
    simpa [rowInvariantPreserved,rowInvariant,namedBoth,Formula.not,Formula.encode,both,neg] using hi
  have hp := Context.conjunctionLeft hparts
  have hr := Context.conjunctionRight hparts
  have hc : Context Γ (replace 0 1 (coverage 7)).encode :=
    .mp (Context.conjunctionLeft hr) (.mp hn (.mp hs (.closed outside_coverage)))
  have hg : Context Γ (replace 0 1 (noGarbage 7)).encode :=
    .mp (Context.conjunctionRight hr) (.mp hn (.mp hs (.closed outside_no_garbage)))
  have h := Context.conjunctionIntro hp (Context.conjunctionIntro hc hg)
  change Context Γ (replace 0 1 (rowInvariantPreserved 7)).encode
  rw [show replace 0 1 (rowInvariantPreserved 7) = namedBoth (oldPreserved 7)
    (namedBoth (replace 0 1 (coverage 7)) (replace 0 1 (noGarbage 7))) from newInv_shape]
  simpa [Γ,namedBoth,Formula.not,Formula.encode,both,neg] using h

theorem outside_step_certificate : theoremCode (certificate outside_step) =
    imp (successorCode 0 1 2) (imp (neg (member 31 0))
      (imp (rowInvariantPreserved 7).encode (replace 0 1 (rowInvariantPreserved 7)).encode)) :=
  certificate_correct outside_step
/-- The outside branch transports an existential graph witness while retaining
that very graph value in the proof. -/
def outside_exists : KDerivation (imp (successorCode 0 1 2)
    (imp (neg (member 31 0))
      (imp (existsCode 7 (rowInvariantPreserved 7).encode)
        (existsCode 7 (replace 0 1 (rowInvariantPreserved 7)).encode)))) := by
  let H : Formula := namedBoth (namedSuccessor 0 1 2) (Formula.member 31 0).not
  have hlocal : KDerivation (imp H.encode
      (imp (rowInvariantPreserved 7).encode (replace 0 1 (rowInvariantPreserved 7)).encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [H.encode]
    have hh : Context Γ H.encode := .head _ _
    have hp : Context Γ (both (successorCode 0 1 2) (neg (member 31 0))) := by
      simpa [H,namedSuccessor,namedSuccessorBody,namedBoth,namedEither,Formula.encode,
        Formula.not,successorCode,both,neg,either] using hh
    exact .mp (Context.conjunctionRight hp) (.mp (Context.conjunctionLeft hp) (.closed outside_step))
  have hlift := conditionalExistsCongr 7 (H.vacuity 7 (by decide)) hlocal
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [neg (member 31 0),successorCode 0 1 2]
  have hn : Context Γ (neg (member 31 0)) := .head _ _
  have hs : Context Γ (successorCode 0 1 2) := .hypothesis (by simp [Γ])
  have hh : Context Γ H.encode := by
    simpa [H,namedSuccessor,namedSuccessorBody,namedBoth,namedEither,Formula.encode,
      Formula.not,successorCode,both,neg,either] using Context.conjunctionIntro hs hn
  exact .mp hh (.closed hlift)

theorem outside_exists_certificate : theoremCode (certificate outside_exists) =
    imp (successorCode 0 1 2) (imp (neg (member 31 0))
      (imp (existsCode 7 (rowInvariantPreserved 7).encode)
        (existsCode 7 (replace 0 1 (rowInvariantPreserved 7)).encode))) :=
  certificate_correct outside_exists
end PASoundness.PAtoCompactFixedFirstOutsideStep
#print axioms PASoundness.PAtoCompactFixedFirstOutsideStep.outside_step
#print axioms PASoundness.PAtoCompactFixedFirstOutsideStep.outside_step_certificate
#print axioms PASoundness.PAtoCompactFixedFirstOutsideStep.outside_exists
#print axioms PASoundness.PAtoCompactFixedFirstOutsideStep.outside_exists_certificate
