import PASoundness.PAtoCompactAdditionTopWitnessUnequal
import PASoundness.PAtoCompactAdditionOldTargetWitnessTransfer
import PASoundness.PAtoCompactSuccLeftUniqueTransfer

/-! The top-target branch for the distinct-top addition graph: strengthen the
existing unguarded uniqueness witness, alpha-convert its bound source label,
and transport the target along an explicit equality. This is one K bijection
case, not a full bijection, addition totality, or PA proof translation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionTopTargetTransport
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactAdditionSuccessorGraphClean
open PASoundness.PAtoCompactAdditionTopWitnessUnequal PASoundness.PAtoCompactAdditionOldTargetWitnessTransfer
open PASoundness.PAtoCompactSuccLeftUniqueTransfer
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def guarded3 : Formula := namedBoth (.member 38 3)
  (namedBoth (graphFormula 9 3 32)
    (.all 4 (.imp (namedBoth (.member 38 4) (graphFormula 9 4 32)) (.equal 4 3))))
private def guarded2 : Formula := namedBoth (.member 38 2)
  (namedBoth (graphFormula 9 2 32)
    (.all 4 (.imp (namedBoth (.member 38 4) (graphFormula 9 4 32)) (.equal 4 2))))
private def desired : Formula := .ex 2 newWitnessBody

/-- A top-source uniqueness condition remains valid with an additional domain
condition on each competing source. -/
def guard_top_witness : KDerivation (imp (existsCode 3 topTargetWitness.encode)
    (existsCode 3 guarded3.encode)) := by
  have hp : KDerivation (imp topTargetWitness.encode guarded3.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    have ho : Context [topTargetWitness.encode] topTargetWitness.encode := .head _ _
    have hm : Context [topTargetWitness.encode] (member 38 3) := Context.conjunctionLeft ho
    have he : Context [topTargetWitness.encode] (graphFormula 9 3 32).encode :=
      Context.conjunctionLeft (Context.conjunctionRight ho)
    have hu : Context [topTargetWitness.encode] (allCode 4
        (imp (graphFormula 9 4 32).encode (equal 4 3))) :=
      Context.conjunctionRight (Context.conjunctionRight ho)
    have hguard := KDerivation.generalize 4 (add_target_guard
      (graphFormula 9 4 32).encode (member 38 4) (equal 4 3))
    have hv : Context [topTargetWitness.encode] (allCode 4
        (imp (both (member 38 4) (graphFormula 9 4 32).encode) (equal 4 3))) :=
      Context.allMP hu (.closed hguard)
    exact Context.conjunctionIntro hm (Context.conjunctionIntro he hv)
  exact existsCongr 3 hp

/-- Exact guarded top-target preimage at target 28, under the explicit
object-level equality of target 28 with the newly adjoined target 32. -/
def top_target_case : KDerivation (imp suffix (imp (successorCode 31 38 39)
    (imp (adjoinCode 6 11 9 16) (imp (pairFormula 11 31 32).encode
      (imp oldClean.encode (imp (equal 28 32) desired.encode)))))) := by
  have hα := (existentialAlpha 3 2 guarded3 (by decide) (by decide) (by decide)).1
  have hs : replace 3 2 guarded3 = guarded2 := by decide
  rw [hs] at hα
  have hr := (equalityReplace 28 32 desired (by decide) (by decide)).2
  have he : replace 28 32 desired = .ex 2 guarded2 := by decide
  rw [he] at hr
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [equal 28 32,oldClean.encode,(pairFormula 11 31 32).encode,
    adjoinCode 6 11 9 16,successorCode 31 38 39,suffix]
  have heq : Context Γ (equal 28 32) := .head _ _
  have hc : Context Γ oldClean.encode := .hypothesis (by simp [Γ])
  have hp : Context Γ (pairFormula 11 31 32).encode := .hypothesis (by simp [Γ])
  have hg : Context Γ (adjoinCode 6 11 9 16) := .hypothesis (by simp [Γ])
  have hs' : Context Γ (successorCode 31 38 39) := .hypothesis (by simp [Γ])
  have hf : Context Γ suffix := .hypothesis (by simp [Γ])
  have hw : Context Γ (existsCode 3 topTargetWitness.encode) :=
    .mp hc (.mp hp (.mp hg (.mp hs' (.mp hf (.closed top_target_witness)))))
  have hguard : Context Γ (existsCode 3 guarded3.encode) := .mp hw (.closed guard_top_witness)
  have hw2 : Context Γ (existsCode 2 guarded2.encode) := .mp hguard (.closed hα)
  exact .mp hw2 (.mp heq (.closed hr))

theorem top_target_case_certificate : theoremCode (certificate top_target_case) =
    imp suffix (imp (successorCode 31 38 39) (imp (adjoinCode 6 11 9 16)
      (imp (pairFormula 11 31 32).encode (imp oldClean.encode
        (imp (equal 28 32) desired.encode))))) := certificate_correct top_target_case
end PASoundness.PAtoCompactAdditionTopTargetTransport
#print axioms PASoundness.PAtoCompactAdditionTopTargetTransport.guard_top_witness
#print axioms PASoundness.PAtoCompactAdditionTopTargetTransport.top_target_case
#print axioms PASoundness.PAtoCompactAdditionTopTargetTransport.top_target_case_certificate
