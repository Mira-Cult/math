import PASoundness.PAtoCompactAdditionEmptySuffix
import PASoundness.PAtoCompactAdditionSuffixClosed
import PASoundness.PAtoCompactAdditionTwoZeros
import PASoundness.PAtoCompactAdditionZeroAllocated

/-! K right-zero witnesses retaining the left operand as the literal cut.
This fixed-name base case is not general addition totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLiteralCutBaseWitness
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactAdditionEmptySuffix
open PASoundness.PAtoCompactAdditionSuffixClosed PASoundness.PAtoCompactAdditionTwoZeros
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactAdditionZeroAllocated
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private def sf : Formula := .ex 34 suffixFormula
private def selfSuffix : Formula := replace 33 30 (replace 32 30 suffixFormula)

/-- K constructs a suffix of a set by itself, with both occurrences of the
same set represented by name 30. -/
def self_suffix_exists : KDerivation (existsCode 34 selfSuffix.encode) := by
  have h : KDerivation sf.encode := by simpa [sf,Formula.encode] using suffix_exists
  have h1 := KDerivation.mp (.generalize 32 h)
    (universalInstance 32 30 sf (by decide) (by decide) (by decide))
  have h2 := KDerivation.mp (.generalize 33 h1)
    (universalInstance 33 30 (replace 32 30 sf) (by decide) (by decide) (by decide))
  have hs : replace 33 30 (replace 32 30 sf) = .ex 34 selfSuffix := by decide
  rw [hs] at h2
  exact h2

private def emptySource : Formula := .imp (.equal 32 33)
  (.imp suffixFormula (.all 37 (.imp (.member 34 37) .bottom)))
private theorem emptySource_code : emptySource.encode =
    imp (equal 32 33) (imp (filterGraph 32 34 35 (neg (member 33 35))) (zeroCode 34 37)) := by rfl

/-- The self-filtered suffix is zero; the alias is obtained by capture-safe
specialization of the distinct-name K theorem. -/
def self_suffix_is_zero : KDerivation (imp selfSuffix.encode (zeroCode 34 37)) := by
  have h : KDerivation emptySource.encode := by rw [emptySource_code]; exact equal_cut_empty_suffix 32 33 34 35 37 (by decide)
  have h1 := KDerivation.mp (.generalize 32 h)
    (universalInstance 32 30 emptySource (by decide) (by decide) (by decide))
  have h2 := KDerivation.mp (.generalize 33 h1)
    (universalInstance 33 30 (replace 32 30 emptySource) (by decide) (by decide) (by decide))
  have hs : replace 33 30 (replace 32 30 emptySource) =
      .imp (.equal 30 30) (.imp selfSuffix (.all 37 (.imp (.member 34 37) .bottom))) := by decide
  rw [hs] at h2
  exact .mp (equalityReflexive 30) h2

/-- A supplied zero right input and the constructed self-filtered suffix are
isomorphic. -/
def self_suffix_equivalent_zero : KDerivation (imp (zeroCode 31 36)
    (existsCode 34 (namedBoth selfSuffix (equivAt 31 34)).encode)) := by
  let Z : Formula := .all 36 (.imp (.member 31 36) .bottom)
  let B : Formula := namedBoth selfSuffix (equivAt 31 34)
  have hv : KDerivation (imp Z.encode (allCode 34 Z.encode)) := Z.vacuity 34 (by decide)
  have hp : KDerivation (imp Z.encode (imp selfSuffix.encode B.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [selfSuffix.encode,Z.encode]
    have hf : Context Γ selfSuffix.encode := .head _ _
    have hz : Context Γ (zeroCode 31 36) := by exact .hypothesis (by simp [Γ,Z,Formula.encode,zeroCode,neg])
    have hs : Context Γ (zeroCode 34 37) := .mp hf (.closed self_suffix_is_zero)
    have he : Context Γ (PAtoCompactOrdinalAddition.equivAt 31 34).encode := .mp hs (.mp hz (.closed two_zeros_equivalent_addition))
    exact Context.conjunctionIntro hf he
  have hc := conditionalExistsCongr 34 hv hp
  apply Context.closeEmpty
  apply Context.deduction
  have hz : Context [Z.encode] Z.encode := .head _ _
  have hr : Context [Z.encode] (existsCode 34 B.encode) :=
    .mp (.closed self_suffix_exists) (.mp hz (.closed hc))
  simpa [Z,Formula.encode,zeroCode,neg,B] using hr

theorem self_suffix_equivalent_zero_certificate :
    theoremCode (certificate self_suffix_equivalent_zero) =
      imp (zeroCode 31 36) (existsCode 34 (namedBoth selfSuffix (equivAt 31 34)).encode) :=
  certificate_correct self_suffix_equivalent_zero
end PASoundness.PAtoCompactLiteralCutBaseWitness
#print axioms PASoundness.PAtoCompactLiteralCutBaseWitness.self_suffix_exists
#print axioms PASoundness.PAtoCompactLiteralCutBaseWitness.self_suffix_is_zero
#print axioms PASoundness.PAtoCompactLiteralCutBaseWitness.self_suffix_equivalent_zero
#print axioms PASoundness.PAtoCompactLiteralCutBaseWitness.self_suffix_equivalent_zero_certificate
