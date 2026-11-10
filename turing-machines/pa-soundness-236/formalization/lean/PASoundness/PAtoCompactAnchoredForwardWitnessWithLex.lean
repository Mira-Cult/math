import PASoundness.PAtoCompactAnchoredForwardWitnessLift
import PASoundness.PAtoCompactForwardContextWithLex

/-! Attach the established lex clause inside the same nested anchored
witness package as the forward shared context. No second row graph, suffix
map or other witness is chosen. This does not establish the product forward
or reverse clauses, multiplication totality or PA soundness. -/
namespace PASoundness.PAtoCompactAnchoredForwardWitnessWithLex
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactAnchoredProductWitnessPackage PASoundness.PAtoCompactCleanSuffixRowPackage
open PASoundness.PAtoCompactAnchoredLexSharedProjection PASoundness.PAtoCompactScopedRowLexLift
open PASoundness.PAtoCompactAnchoredForwardWitnessLift PASoundness.PAtoCompactForwardContextWithLex
set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Retain the original cut, old graph and clean map while placing the
forward context and lex clause under the same row-graph binder. -/
def retainedLexResult : Nat := nested suffixData.encode oldBody.encode cleanMatrix.encode
  contextWithLex.encode

private def retain_left (a b c : Nat) (h : KDerivation (imp b c)) :
    KDerivation (imp (both a b) (both a c)) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [both a b]
  have hp : Context Γ (both a b) := .head _ _
  exact Context.conjunctionIntro (Context.conjunctionLeft hp)
    (.mp (Context.conjunctionRight hp) (.closed h))

/-- Lift the closed same-graph context-to-lex derivation through all four
existing witness binders, retaining each earlier conjunct. -/
def attach_inside : KDerivation (imp retainedResult retainedLexResult) := by
  have h64 := existsCongr 64 attach_lex
  have h6 := existsCongr 6 (retain_left cleanMatrix.encode _ _ h64)
  have h10 := existsCongr 10 (retain_left oldBody.encode _ _ h6)
  have h40 := existsCongr 40 (retain_left suffixData.encode _ _ h10)
  simpa only [retainedResult,retainedLexResult,nested] using h40

/-- The actual original anchored package and the explicit candidate/successor
guards yield the context and lex clause for the same four witnesses. -/
def retain_forward_with_lex : KDerivation
    (imp guards.encode (imp anchoredResult.encode retainedLexResult)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [anchoredResult.encode,guards.encode]
  have ha : Context Γ anchoredResult.encode := .head _ _
  have hg : Context Γ guards.encode := .hypothesis (by simp [Γ])
  exact .mp (.mp ha (.mp hg (.closed retain_forward))) (.closed attach_inside)

theorem retain_forward_with_lex_certificate :
    theoremCode (certificate retain_forward_with_lex) =
      imp guards.encode (imp anchoredResult.encode retainedLexResult) := certificate_correct _
end PASoundness.PAtoCompactAnchoredForwardWitnessWithLex
#print axioms PASoundness.PAtoCompactAnchoredForwardWitnessWithLex.attach_inside
#print axioms PASoundness.PAtoCompactAnchoredForwardWitnessWithLex.retain_forward_with_lex
#print axioms PASoundness.PAtoCompactAnchoredForwardWitnessWithLex.retain_forward_with_lex_certificate
