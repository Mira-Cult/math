import PASoundness.PAtoCompactProductOutputForwardAlignment
import PASoundness.PAtoCompactProductOutputReverseClauseAll

/-! Align the alpha-renamed explicit reverse clause with the canonical target
product reverse formula by a finite-K conjunction reassociation. Order and
graph existence are separate. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputReverseAlignment

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactProductOutputClauseAlpha
open PASoundness.PAtoCompactProductOutputForwardAlignment PASoundness.PAtoCompactProductOutputReverseClauseAll

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Move the final conjunct into a right-associated three-conjunct body. -/
def both_assoc4 (a b c d : Nat) : KDerivation
    (imp (both (both a (both b c)) d) (both a (both b (both c d)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [both (both a (both b c)) d]
  have h : Context Γ (both (both a (both b c)) d) := .head _ _
  have hs := Context.conjunctionLeft h
  have ht := Context.conjunctionRight hs
  exact Context.conjunctionIntro (Context.conjunctionLeft hs)
    (Context.conjunctionIntro (Context.conjunctionLeft ht)
      (Context.conjunctionIntro (Context.conjunctionRight ht) (Context.conjunctionRight h)))

def uniqueBody : Formula := .all 7 (.all 8 (.imp
  (namedBoth (.member 43 7) (namedBoth (.member 44 8) (outputTriple 7 8 5)))
  (namedBoth (.equal 7 3) (.equal 8 4))))
def mappedBody : Formula := namedBoth (namedBoth (.member 43 3)
  (namedBoth (.member 44 4) (outputTriple 3 4 5))) uniqueBody
def canonicalBody : Formula := namedBoth (.member 43 3)
  (namedBoth (.member 44 4) (namedBoth (outputTriple 3 4 5) uniqueBody))
def mappedReverse : Formula := .all 5 (.imp (.member 42 5) (.ex 3 (.ex 4 mappedBody)))
def canonicalReverse : Formula := replace 6 58 (replace 2 42 (replace 1 44 (replace 0 43
  PAtoCompactMultiplicationCandidate.reverseFormula)))

theorem mapped_reverse_shape : reverseMapped = mappedReverse := by decide
theorem canonical_reverse_shape : canonicalReverse = .all 5 (.imp (.member 42 5)
  (.ex 3 (.ex 4 canonicalBody))) := by decide

def mapped_to_canonical : KDerivation (imp reverseMapped.encode canonicalReverse.encode) := by
  have hb : KDerivation (imp mappedBody.encode canonicalBody.encode) := by
    simpa [mappedBody, canonicalBody, namedBoth, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using
      both_assoc4 (member 43 3) (member 44 4) (outputTriple 3 4 5).encode uniqueBody.encode
  have he4 := existsCongr 4 hb
  have he3 := existsCongr 3 he4
  have hi := implicationCongr (CompactHilbertBasis.identity (member 42 5)) he3
  have ha := allCongr 5 hi
  simpa [mapped_reverse_shape, mappedReverse, canonical_reverse_shape, CompactNamed.Formula.encode] using ha

def reverse_alignment : KDerivation (imp reverseClause.encode canonicalReverse.encode) :=
  compose reverse_alpha.forward mapped_to_canonical

theorem reverse_alignment_certificate : theoremCode (certificate reverse_alignment) =
    imp reverseClause.encode canonicalReverse.encode := certificate_correct _

end PASoundness.PAtoCompactProductOutputReverseAlignment

#print axioms PASoundness.PAtoCompactProductOutputReverseAlignment.both_assoc4
#print axioms PASoundness.PAtoCompactProductOutputReverseAlignment.mapped_to_canonical
#print axioms PASoundness.PAtoCompactProductOutputReverseAlignment.reverse_alignment
#print axioms PASoundness.PAtoCompactProductOutputReverseAlignment.reverse_alignment_certificate
