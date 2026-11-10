import PASoundness.PAtoCompactProductOutputReverseAlignment
import PASoundness.PAtoCompactProductOutputLexGraphAll

/-! Align the collected graph's quantified lex-order clause with the literal
canonical target product order clause. Two universal commutations and a
finite-K endpoint-guard permutation are explicit; no semantic soundness or
product existence is used. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputOrderAlignment

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactProductOutputClauseAlpha
open PASoundness.PAtoCompactProductOutputForwardAlignment PASoundness.PAtoCompactProductOutputLexGraphAll

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def lex : Formula := namedEither (.member 7 3) (namedBoth (.equal 3 7) (.member 8 4))
def comparison : Formula := namedBoth (.imp (.member 9 5) lex) (.imp lex (.member 9 5))
def mappedGuard : Formula := namedBoth (.member 43 3) (namedBoth (.member 44 4)
  (namedBoth (.member 43 7) (namedBoth (.member 44 8) (namedBoth (.member 42 5)
    (namedBoth (.member 42 9) (namedBoth (outputTriple 3 4 5) (outputTriple 7 8 9)))))))
def canonicalGuard : Formula := namedBoth (.member 43 3) (namedBoth (.member 44 4)
  (namedBoth (.member 42 5) (namedBoth (.member 43 7) (namedBoth (.member 44 8)
    (namedBoth (.member 42 9) (namedBoth (outputTriple 3 4 5) (outputTriple 7 8 9)))))))
def mappedBody : Formula := .imp mappedGuard comparison
def canonicalBody : Formula := .imp canonicalGuard comparison
def mappedOrder : Formula := .all 3 (.all 4 (.all 7 (.all 8 (.all 5 (.all 9 mappedBody)))))
def swappedOrder : Formula := .all 3 (.all 4 (.all 5 (.all 7 (.all 8 (.all 9 mappedBody)))))
def canonicalOrder : Formula := replace 6 58 (replace 2 42 (replace 1 44 (replace 0 43
  PAtoCompactMultiplicationCandidate.lexFormula)))

theorem mapped_order_shape : orderMapped = mappedOrder := by decide
theorem canonical_order_shape : canonicalOrder = .all 3 (.all 4 (.all 5 (.all 7 (.all 8 (.all 9 canonicalBody))))) := by decide

/-- The canonical endpoint order implies the explicit graph-order guard. -/
def guard_permutation : KDerivation (imp canonicalGuard.encode mappedGuard.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [canonicalGuard.encode]
  have hg : Context Γ canonicalGuard.encode := .head _ _
  have hg' : Context Γ (both (member 43 3) (both (member 44 4) (both (member 42 5)
      (both (member 43 7) (both (member 44 8) (both (member 42 9)
        (both (outputTriple 3 4 5).encode (outputTriple 7 8 9).encode))))))) := by
    simpa [canonicalGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hg
  have h1 := Context.conjunctionLeft hg'
  have t := Context.conjunctionRight hg'
  have h2 := Context.conjunctionLeft t
  have t := Context.conjunctionRight t
  have h5 := Context.conjunctionLeft t
  have t := Context.conjunctionRight t
  have h3 := Context.conjunctionLeft t
  have t := Context.conjunctionRight t
  have h4 := Context.conjunctionLeft t
  have t := Context.conjunctionRight t
  have h6 := Context.conjunctionLeft t
  have hrest := Context.conjunctionRight t
  simpa [mappedGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
    Context.conjunctionIntro h1 (Context.conjunctionIntro h2 (Context.conjunctionIntro h3
      (Context.conjunctionIntro h4 (Context.conjunctionIntro h5 (Context.conjunctionIntro h6 hrest)))))

def mapped_to_canonical : KDerivation (imp orderMapped.encode canonicalOrder.encode) := by
  have hswap1 := allCongr 7 (allCommute 8 5 (allCode 9 mappedBody.encode))
  have hswap2 := allCommute 7 5 (allCode 8 (allCode 9 mappedBody.encode))
  have hswap := allCongr 3 (allCongr 4 (compose hswap1 hswap2))
  have hb : KDerivation (imp mappedBody.encode canonicalBody.encode) := by
    simpa [mappedBody, canonicalBody, CompactNamed.Formula.encode] using
      implicationCongr guard_permutation (CompactHilbertBasis.identity comparison.encode)
  have hbody := allCongr 3 (allCongr 4 (allCongr 5 (allCongr 7 (allCongr 8 (allCongr 9 hb)))))
  have h := compose hswap hbody
  simpa [mapped_order_shape, mappedOrder, canonical_order_shape, CompactNamed.Formula.encode] using h

def order_alignment : KDerivation (imp graphOrder.encode canonicalOrder.encode) :=
  compose order_alpha.forward mapped_to_canonical

theorem order_alignment_certificate : theoremCode (certificate order_alignment) =
    imp graphOrder.encode canonicalOrder.encode := certificate_correct _

end PASoundness.PAtoCompactProductOutputOrderAlignment

#print axioms PASoundness.PAtoCompactProductOutputOrderAlignment.guard_permutation
#print axioms PASoundness.PAtoCompactProductOutputOrderAlignment.mapped_to_canonical
#print axioms PASoundness.PAtoCompactProductOutputOrderAlignment.order_alignment
#print axioms PASoundness.PAtoCompactProductOutputOrderAlignment.order_alignment_certificate
