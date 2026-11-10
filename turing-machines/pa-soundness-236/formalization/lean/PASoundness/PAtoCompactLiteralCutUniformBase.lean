import PASoundness.PAtoCompactLiteralCutAdditionDefinition
import PASoundness.PAtoCompactLiteralCutBaseWitness
import PASoundness.PAtoCompactAdditionInductionUniformBase

/-! The zero base of candidate induction for addition with literal cut.
This chooses the output equal to the first input and retains the exact cut;
it does not prove the successor step or general totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLiteralCutUniformBase
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactUniformBase
open PASoundness.PAtoCompactLiteralCutAdditionDefinition PASoundness.PAtoCompactLiteralCutBaseWitness
open PASoundness.PAtoCompactAdditionZeroAllocated PASoundness.PAtoCompactDomainClassification
open PASoundness.PAtoCompactVacuousUniversal PASoundness.PAtoCompactAdjunction
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def B : Formula := namedBoth (replace 33 30 (replace 32 30 suffixFormula))
  (PAtoCompactOrdinalAddition.equivAt 31 34)
private def body : Formula := andF (domainAt 100 32) literalCut
private def bodyAt30 : Formula := replace 32 30 body
private def cutAt30 : Formula := replace 32 30 literalCut
private def Q : Formula := namedBoth (namedEither (.equal 30 30) (.member 30 30)) B

private theorem cutAt30_shape : cutAt30 = .ex 34 Q := by decide
private theorem bodyAt30_shape : bodyAt30 = andF (domainAt 100 30) cutAt30 := by
  simp [bodyAt30, body, cutAt30, andF, Formula.not, replace, replace_domainAt 100 32 30 (by decide)]

/-- A zero right operand yields the pinned-cut relation with output equal to
first input 30; the suffix witness is constructed in K. -/
def zero_literal_cut : KDerivation (imp (zeroCode 31 36) cutAt30.encode) := by
  have h : KDerivation (imp B.encode Q.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    have hb : Context [B.encode] B.encode := .head _ _
    have he : Context [B.encode] (either (equal 30 30) (member 30 30)) :=
      Context.disjunctionLeft (.closed (equalityReflexive 30))
    exact Context.conjunctionIntro he hb
  have hc := existsCongr 34 h
  have hs : KDerivation (imp (zeroCode 31 36) (existsCode 34 B.encode)) := by
    have hk := self_suffix_equivalent_zero
    change KDerivation (imp (zeroCode 31 36) (existsCode 34 B.encode)) at hk
    exact hk
  rw [cutAt30_shape]
  exact compose hs hc

/-- Candidate-guarded pinned-cut output exists for a zero right operand. -/
def right_zero_literal_output : KDerivation
    (imp (domainAt 100 30).encode (imp (zeroCode 31 36)
      (existsCode 32 body.encode))) := by
  have hi := exists_variable_intro 32 30 body (by decide) (by decide) (by decide)
  change KDerivation (imp bodyAt30.encode (existsCode 32 body.encode)) at hi
  rw [bodyAt30_shape] at hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [zeroCode 31 36, (domainAt 100 30).encode]
  have hz : Context Γ (zeroCode 31 36) := .head _ _
  have hd : Context Γ (domainAt 100 30).encode := .hypothesis (by simp [Γ])
  have hc : Context Γ cutAt30.encode := .mp hz (.closed zero_literal_cut)
  have hp : Context Γ (andF (domainAt 100 30) cutAt30).encode := by
    simpa [andF, Formula.not, Formula.encode, both, neg] using Context.conjunctionIntro hd hc
  exact .mp hp (.closed hi)

private def fixedBody : Formula := .imp (domainAt 100 30)
  (.imp (.all 36 (.imp (.member 31 36) .bottom)) (.ex 32 body))
private theorem fixedBody_code : fixedBody.encode =
    imp (domainAt 100 30).encode (imp (zeroCode 31 36) (existsCode 32 body.encode)) := by rfl
private theorem replacedBody_code : (replace 31 205 fixedBody).encode =
    imp (domainAt 100 30).encode (imp (zeroCode 205 36)
      (existsCode 32 (andF (domainAt 100 32) (replace 31 205 literalCut)).encode)) := by
  have h : replace 31 205 fixedBody = .imp (domainAt 100 30)
      (.imp (.all 36 (.imp (.member 205 36) .bottom))
        (.ex 32 (andF (domainAt 100 32) (replace 31 205 literalCut)))) := by decide
  rw [h]; rfl
private theorem replacedPredicate_code : (replace 31 205 predicate).encode =
    imp (domainAt 100 30).encode
      (existsCode 32 (andF (domainAt 100 32) (replace 31 205 literalCut)).encode) := by
  have h : replace 31 205 predicate = .imp (domainAt 100 30)
      (.ex 32 (andF (domainAt 100 32) (replace 31 205 literalCut))) := by decide
  rw [h]; rfl

private def specialize : KDerivation ((replace 31 205 fixedBody).encode) := by
  have h : KDerivation fixedBody.encode := by rw [fixedBody_code]; exact right_zero_literal_output
  exact .mp (.generalize 31 h) (universalInstance 31 205 fixedBody (by decide) (by decide) (by decide))

/-- Exact uniform zero base for the pinned-cut predicate. -/
def uniform_base : KDerivation (uniformBaseCode 31 205 207 predicate) := by
  apply KDerivation.generalize 205
  rw [replacedPredicate_code]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(domainAt 100 30).encode,zeroCode 205 207]
  have hd : Context Γ (domainAt 100 30).encode := .head _ _
  have hz : Context Γ (zeroCode 205 207) := .hypothesis (by simp [Γ])
  have hz' : Context Γ (zeroCode 205 36) :=
    .mp hz (.closed (zero_test_rename 205 207 36 (by decide) (by decide) (by decide)))
  have hi : KDerivation (imp (domainAt 100 30).encode
      (imp (zeroCode 205 36)
        (existsCode 32 (andF (domainAt 100 32) (replace 31 205 literalCut)).encode))) := by
    simpa only [replacedBody_code] using specialize
  exact .mp hz' (.mp hd (.closed hi))

theorem uniform_base_certificate : theoremCode (certificate uniform_base) =
    uniformBaseCode 31 205 207 predicate := certificate_correct uniform_base
end PASoundness.PAtoCompactLiteralCutUniformBase
#print axioms PASoundness.PAtoCompactLiteralCutUniformBase.zero_literal_cut
#print axioms PASoundness.PAtoCompactLiteralCutUniformBase.right_zero_literal_output
#print axioms PASoundness.PAtoCompactLiteralCutUniformBase.uniform_base
#print axioms PASoundness.PAtoCompactLiteralCutUniformBase.uniform_base_certificate
