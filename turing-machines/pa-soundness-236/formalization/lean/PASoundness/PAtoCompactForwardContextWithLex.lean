import PASoundness.PAtoCompactMultiplicationForwardSharedContext
import PASoundness.PAtoCompactMultiplicationRowWithLex

/-! Add the proved lexicographic clause to the forward shared context on the
same row graph 64 and suffix map 6. This is a finite K implication, not a
product bijection or multiplication theorem. -/
namespace PASoundness.PAtoCompactForwardContextWithLex
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactMultiplicationForwardSharedContext
open PASoundness.PAtoCompactMultiplicationRowWithLex PASoundness.PAtoCompactProductNewLexShape
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The context and lex clause have one shared graph witness, not two
independently chosen graphs. -/
def contextWithLex : Formula := namedBoth context newLex

/-- The existing scoped context entails the conjunction for the same free
labels, including the original graph and suffix-map names. -/
def attach_lex : KDerivation (imp context.encode contextWithLex.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [context.encode]
  have hc : Context Γ context.encode := .head _ _
  have hp := Context.mp hc (.closed project_shared)
  have hr := Context.mp hc (.closed project_row)
  have hl : Context Γ newLex.encode := .mp hr (.mp hp (.closed lex_from_row))
  simpa [contextWithLex,namedBoth,Formula.not,Formula.encode,both,neg] using
    (Context.conjunctionIntro hc hl)

theorem attach_lex_certificate : theoremCode (certificate attach_lex) =
    imp context.encode contextWithLex.encode := certificate_correct _
end PASoundness.PAtoCompactForwardContextWithLex
#print axioms PASoundness.PAtoCompactForwardContextWithLex.attach_lex
#print axioms PASoundness.PAtoCompactForwardContextWithLex.attach_lex_certificate
