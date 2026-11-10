import PASoundness.PAtoCompactMultiplicationFullPrefixLex
import PASoundness.PAtoCompactMultiplicationFullPrefixNoGarbage

/-! Attach the proved lexicographic clause to the actual full-prefix row
invariant, retaining the same graph witness 64 and suffix map 6. The shared
candidate, cut, old-graph and suffix-graph assumptions remain explicit. This
is not row existence, product bijectivity, multiplication totality, or a PA
proof translation. -/
namespace PASoundness.PAtoCompactMultiplicationRowWithLex
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFixedFirstRowGraph64
open PASoundness.PAtoCompactMultiplicationLexSharedContext PASoundness.PAtoCompactProductNewLexShape
open PASoundness.PAtoCompactMultiplicationFullPrefixLex
open PASoundness.PAtoCompactMultiplicationFullPrefixNoGarbage
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Both properties refer to the same displayed row graph name 64. -/
def rowWithLex : Formula := namedBoth rowBody64 newLex

/-- Given the actual row invariant, the explicit common assumptions prove the
exact quantified lexicographic clause for that graph. -/
def lex_from_row : KDerivation (imp sharedPremise.encode
    (imp rowBody64.encode newLex.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [rowBody64.encode,sharedPremise.encode]
  have hr : Context Γ rowBody64.encode := .head _ _
  have hp : Context Γ sharedPremise.encode := .hypothesis (by simp [Γ])
  have hn : Context Γ fullNoGarbage.encode := by
    simpa [fullNoGarbage] using (Context.mp hr (.closed full_prefix_no_garbage))
  exact .mp hn (.mp hp (.closed full_prefix_lex))

/-- An already-existing row graph can be retained together with its lex
clause under one existential: the two conjuncts use the same graph witness. -/
def retain_row_with_lex : KDerivation (imp sharedPremise.encode
    (imp (existsCode 64 rowBody64.encode) (existsCode 64 rowWithLex.encode))) := by
  have hp : KDerivation (imp sharedPremise.encode (allCode 64 sharedPremise.encode)) :=
    sharedPremise.vacuity 64 (by decide)
  have hlocal : KDerivation (imp sharedPremise.encode (imp rowBody64.encode rowWithLex.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [rowBody64.encode,sharedPremise.encode]
    have hr : Context Γ rowBody64.encode := .head _ _
    have hp' : Context Γ sharedPremise.encode := .hypothesis (by simp [Γ])
    have hl : Context Γ newLex.encode := .mp hr (.mp hp' (.closed lex_from_row))
    simpa [rowWithLex,namedBoth,Formula.not,Formula.encode,both,neg] using
      (Context.conjunctionIntro hr hl)
  exact conditionalExistsCongr 64 hp hlocal

theorem lex_from_row_certificate : theoremCode (certificate lex_from_row) =
    imp sharedPremise.encode (imp rowBody64.encode newLex.encode) := certificate_correct _

theorem retain_row_with_lex_certificate : theoremCode (certificate retain_row_with_lex) =
    imp sharedPremise.encode (imp (existsCode 64 rowBody64.encode)
      (existsCode 64 rowWithLex.encode)) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationRowWithLex
#print axioms PASoundness.PAtoCompactMultiplicationRowWithLex.lex_from_row
#print axioms PASoundness.PAtoCompactMultiplicationRowWithLex.retain_row_with_lex
#print axioms PASoundness.PAtoCompactMultiplicationRowWithLex.lex_from_row_certificate
#print axioms PASoundness.PAtoCompactMultiplicationRowWithLex.retain_row_with_lex_certificate
