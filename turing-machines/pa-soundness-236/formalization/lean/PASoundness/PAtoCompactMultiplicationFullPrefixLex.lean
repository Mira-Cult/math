import PASoundness.PAtoCompactMultiplicationLexQuantified

/-! Capture-safe specialization of the product lexicographic theorem from a
free prefix label to the actual full row domain. The row index domain and
prefix intentionally share label 31. The shared assumptions and the literal
no-garbage hypothesis remain explicit; this constructs neither a row graph
nor a product bijection, multiplication totality or PA proof translation. -/
namespace PASoundness.PAtoCompactMultiplicationFullPrefixLex
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactMultiplicationLexSharedContext
open PASoundness.PAtoCompactProductNewLexShape
open PASoundness.PAtoCompactMultiplicationLexQuantified
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Actual full-prefix no-garbage condition: the prefix label 0 has been
replaced by the row domain label 31, intentionally allowing aliasing. -/
def fullNoGarbage : Formula := replace 0 31 (noGarbage 64)

private def source : Formula := .imp sharedPremise (.imp (noGarbage 64) newLex)

/-- Syntax-only check: specializing the prefix changes neither the shared
premises nor the target lexicographic formula. -/
theorem source_specialized : replace 0 31 source =
    .imp sharedPremise (.imp fullNoGarbage newLex) := by decide

/-- The exact quantified product lexicographic clause for the full row
follows from the same shared assumptions and the specialized no-garbage
condition. The construction uses K generalization and universal instantiation. -/
def full_prefix_lex : KDerivation (imp sharedPremise.encode
    (imp fullNoGarbage.encode newLex.encode)) := by
  have h : KDerivation source.encode := lex_clause
  have hs := universalInstance 0 31 source (by decide) (by decide) (by decide)
  rw [source_specialized] at hs
  have hout := KDerivation.mp (.generalize 0 h) hs
  simpa [Formula.encode] using hout

theorem full_prefix_lex_certificate : theoremCode (certificate full_prefix_lex) =
    imp sharedPremise.encode (imp fullNoGarbage.encode newLex.encode) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationFullPrefixLex
#print axioms PASoundness.PAtoCompactMultiplicationFullPrefixLex.source_specialized
#print axioms PASoundness.PAtoCompactMultiplicationFullPrefixLex.full_prefix_lex
#print axioms PASoundness.PAtoCompactMultiplicationFullPrefixLex.full_prefix_lex_certificate
