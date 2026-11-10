import PASoundness.PAtoCompactQuotSuccInjectiveWitness
import PASoundness.PAtoCompactCancellationGuardInputs
import PASoundness.CompactFreshen

/-! Capture-safe whole-formula endpoint instantiation for fixed quotient
successor cancellation. The four endpoint guards are made reflexive only after
all binders are freshened; this is finite K proof data. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactQuotSuccCancelFreshened
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactQuotSuccInjectiveWitness
open PASoundness.PAtoCompactQuotSuccWitnessFresh PASoundness.PAtoCompactQuotSuccInjectiveRaw
open PASoundness.PAtoCompactEquivalentAliasInstantiation PASoundness.PAtoCompactEquivalentAliasGuardLift
open PASoundness.PAtoCompactCancellationGuardInputs
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def edge41_43 : Formula := replace 0 41 (replace 1 43 equivalentFormula)

def source : Formula := .imp firstAliases (.imp secondAliases
  (.imp (.equal 40 2) (.imp (.equal 41 7) (.imp (.equal 42 5) (.imp (.equal 43 8)
    (.imp edge78 inputEquivalent))))))

def target : Formula := .imp firstAliases (.imp secondAliases
  (.imp (.equal 40 40) (.imp (.equal 41 41) (.imp (.equal 42 42) (.imp (.equal 43 43)
    (.imp edge41_43 inputEquivalent))))))

theorem source_names_lt : ∀ v ∈ source.names, v < 100 := by decide
theorem target_names_lt : ∀ v ∈ target.names, v < 100 := by decide

def freshSource := freshen source 100 source_names_lt
def freshTarget := freshen target 100 target_names_lt

theorem instantiation_syntax :
    replace 8 43 (replace 5 42 (replace 7 41 (replace 2 40 freshSource.formula))) =
      freshTarget.formula := by decide

/-- The proved guarded cancellation with target at noncapturing operand aliases. -/
def source_proof : KDerivation source.encode := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [edge78.encode,equal 43 8,equal 42 5,equal 41 7,equal 40 2,
    secondAliases.encode,firstAliases.encode]
  have he : Context Γ edge78.encode := Context.head _ _
  have h43 : Context Γ (equal 43 8) := .hypothesis (by simp [Γ])
  have h42 : Context Γ (equal 42 5) := .hypothesis (by simp [Γ])
  have h41 : Context Γ (equal 41 7) := .hypothesis (by simp [Γ])
  have h40 : Context Γ (equal 40 2) := .hypothesis (by simp [Γ])
  have h2 : Context Γ secondAliases.encode := .hypothesis (by simp [Γ])
  have h1 : Context Γ firstAliases.encode := .hypothesis (by simp [Γ])
  have hguard : Context Γ (guarded originalAliases).encode :=
    .mp he (.mp h43 (.mp h42 (.mp h41 (.mp h40 (.mp h2 (.mp h1 (.closed witnesses_eliminated)))))))
  exact .mp hguard (.mp h42 (.mp h40 (.closed guard_to_input_equiv)))

/-- First alpha-standardize the entire proof, then simultaneously identify
endpoints with their fresh aliases, and finally convert back. -/
def target_proof : KDerivation target.encode := by
  have h : KDerivation freshSource.formula.encode := .mp source_proof freshSource.equivalent.forward
  have h1 := universalInstance 2 40 freshSource.formula (by decide) (by decide) (by decide)
  have d1 : KDerivation (replace 2 40 freshSource.formula).encode := .mp (.generalize 2 h) h1
  have h2 := universalInstance 7 41 (replace 2 40 freshSource.formula) (by decide) (by decide) (by decide)
  have d2 : KDerivation (replace 7 41 (replace 2 40 freshSource.formula)).encode := .mp (.generalize 7 d1) h2
  have h3 := universalInstance 5 42 (replace 7 41 (replace 2 40 freshSource.formula)) (by decide) (by decide) (by decide)
  have d3 : KDerivation (replace 5 42 (replace 7 41 (replace 2 40 freshSource.formula))).encode := .mp (.generalize 5 d2) h3
  have h4 := universalInstance 8 43 (replace 5 42 (replace 7 41 (replace 2 40 freshSource.formula))) (by decide) (by decide) (by decide)
  have d4 : KDerivation (replace 8 43 (replace 5 42 (replace 7 41 (replace 2 40 freshSource.formula)))).encode := .mp (.generalize 8 d3) h4
  rw [instantiation_syntax] at d4
  exact .mp d4 freshTarget.equivalent.backward

/-- The four endpoint equality guards disappear by K reflexivity. -/
def fixed_quotient_cancellation : KDerivation (imp firstAliases.encode
    (imp secondAliases.encode (imp edge41_43.encode inputEquivalent.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [edge41_43.encode, secondAliases.encode, firstAliases.encode]
  have he : Context Γ edge41_43.encode := Context.head _ _
  have h2 : Context Γ secondAliases.encode := .hypothesis (by simp [Γ])
  have h1 : Context Γ firstAliases.encode := .hypothesis (by simp [Γ])
  have h := Context.mp h2 (Context.mp h1 (Context.closed target_proof))
  have h := Context.mp (Context.closed (equalityReflexive 40)) h
  have h := Context.mp (Context.closed (equalityReflexive 41)) h
  have h := Context.mp (Context.closed (equalityReflexive 42)) h
  have h := Context.mp (Context.closed (equalityReflexive 43)) h
  exact .mp he h

theorem fixed_quotient_cancellation_certificate :
    theoremCode (certificate fixed_quotient_cancellation) = imp firstAliases.encode
      (imp secondAliases.encode (imp edge41_43.encode inputEquivalent.encode)) := certificate_correct _

end PASoundness.PAtoCompactQuotSuccCancelFreshened

#print axioms PASoundness.PAtoCompactQuotSuccCancelFreshened.fixed_quotient_cancellation
#print axioms PASoundness.PAtoCompactQuotSuccCancelFreshened.fixed_quotient_cancellation_certificate
