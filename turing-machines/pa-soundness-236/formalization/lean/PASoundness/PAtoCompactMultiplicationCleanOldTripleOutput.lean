import PASoundness.PAtoCompactMultiplicationCleanOldMemberOutput
import PASoundness.PAtoCompactMultiplicationTripleEdgeAlpha
import PASoundness.PAtoCompactMultiplicationOldTripleIntro

/-! A clean old multiplication graph bounds the output of an actual queried
triple by the old result. The same nested-pair witnesses are retained while
the clean-graph endpoint theorem is applied. This does not construct a new
graph, prove graph uniqueness, or establish multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationCleanOldTripleOutput
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactMultiplicationCleanOldMemberOutput
open PASoundness.PAtoCompactMultiplicationTripleEdgeAlpha
open PASoundness.PAtoCompactMultiplicationOldTripleIntro
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private def oldOuter : Formula := namedBoth (.member 10 63) (pairFormula 63 18 5)
private def expandedOld : Formula := .ex 18 (.ex 63 (namedBoth coordinates oldOuter))
private def tripleImp : Formula := .imp queriedTriple expandedTriple
private def tripleImpOld : Formula := replace 64 10 tripleImp

private def expand_old : KDerivation (imp oldTriple.encode expandedOld.encode) := by
  have h : KDerivation tripleImp.encode := triple_to_expanded
  have h' := KDerivation.mp (.generalize 64 h)
    (universalInstance 64 10 tripleImp (by decide) (by decide) (by decide))
  have hr : tripleImpOld = .imp oldTriple expandedOld := by decide
  change KDerivation tripleImpOld.encode at h'
  rw [hr] at h'
  exact h'

private def point : KDerivation (imp oldClean.encode
    (imp (namedBoth coordinates oldOuter).encode (member 32 5))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(namedBoth coordinates oldOuter).encode,oldClean.encode]
  have h : Context Γ (both coordinates.encode (both (member 10 63)
      (pairFormula 63 18 5).encode)) := by
    have hh : Context Γ (namedBoth coordinates oldOuter).encode := .head _ _
    simpa [oldOuter,namedBoth,Formula.not,Formula.encode,both,neg] using hh
  have hc : Context Γ oldClean.encode := .hypothesis (by simp [Γ])
  have hq : Context Γ query63.encode := by
    have hq' := Context.conjunctionIntro (Context.conjunctionRight (Context.conjunctionRight h))
      (Context.conjunctionLeft h)
    have hs : query63 = namedBoth (pairFormula 63 18 5) coordinates := by decide
    simpa [hs,namedBoth,Formula.not,Formula.encode,both,neg] using hq'
  exact .mp hq (.mp (Context.conjunctionLeft (Context.conjunctionRight h)) (.mp hc (.closed old_output)))

private def lift_exists (x P A B : Nat)
    (hP : KDerivation (imp P (allCode x P))) (hB : KDerivation (imp B (allCode x B)))
    (h : KDerivation (imp P (imp A B))) : KDerivation (imp P (imp (existsCode x A) B)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  have hp : Context [P] P := .head _ _
  have hs : Context [P] (imp A B) := .mp hp (.closed h)
  have hv : ∀ z, z ∈ [P] → KDerivation (imp z (allCode x z)) := by
    intro z hz
    have he : z = P := by simpa using hz
    subst z
    exact hP
  have hall := Context.generalize x hv hs
  exact Context.existsElim hB (.under hall _) (.head _ _)

/-- An actual triple of a clean old graph has its output in the old result.
The graph and its cleanliness are supplied as explicit K antecedents. -/
def old_triple_output : KDerivation (imp oldClean.encode
    (imp oldTriple.encode (member 32 5))) := by
  let body := namedBoth coordinates oldOuter
  have h63 := lift_exists 63 oldClean.encode body.encode (member 32 5)
    (oldClean.vacuity 63 (by decide)) ((Formula.member 32 5).vacuity 63 (by decide)) point
  have h18 := lift_exists 18 oldClean.encode (existsCode 63 body.encode) (member 32 5)
    (oldClean.vacuity 18 (by decide)) ((Formula.member 32 5).vacuity 18 (by decide)) h63
  have h : KDerivation (imp oldClean.encode (imp expandedOld.encode (member 32 5))) := by
    simpa [expandedOld,body,Formula.encode] using h18
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldTriple.encode,oldClean.encode]
  have ht : Context Γ oldTriple.encode := .head _ _
  have hc : Context Γ oldClean.encode := .hypothesis (by simp [Γ])
  exact .mp (.mp ht (.closed expand_old)) (.mp hc (.closed h))

theorem old_triple_output_certificate : theoremCode (certificate old_triple_output) =
    imp oldClean.encode (imp oldTriple.encode (member 32 5)) :=
  certificate_correct old_triple_output
/-- The same clean-graph output bound at competitor output label 9, obtained
by capture-safe universal specialization rather than identifying witnesses. -/
def old_triple_output9 : KDerivation (imp oldClean.encode
    (imp (replace 5 9 oldTriple).encode (member 32 9))) := by
  let f : Formula := .imp oldClean (.imp oldTriple (.member 32 5))
  have h : KDerivation f.encode := old_triple_output
  have h' := KDerivation.mp (.generalize 5 h)
    (universalInstance 5 9 f (by decide) (by decide) (by decide))
  have hs : replace 5 9 f = .imp oldClean (.imp (replace 5 9 oldTriple) (.member 32 9)) := by decide
  rw [hs] at h'
  exact h'

theorem old_triple_output9_certificate : theoremCode (certificate old_triple_output9) =
    imp oldClean.encode (imp (replace 5 9 oldTriple).encode (member 32 9)) :=
  certificate_correct old_triple_output9
end PASoundness.PAtoCompactMultiplicationCleanOldTripleOutput
#print axioms PASoundness.PAtoCompactMultiplicationCleanOldTripleOutput.old_triple_output
#print axioms PASoundness.PAtoCompactMultiplicationCleanOldTripleOutput.old_triple_output_certificate
#print axioms PASoundness.PAtoCompactMultiplicationCleanOldTripleOutput.old_triple_output9
#print axioms PASoundness.PAtoCompactMultiplicationCleanOldTripleOutput.old_triple_output9_certificate
