import PASoundness.PAtoCompactMultiplicationCanonicalFromMatrix
import PASoundness.PAtoCompactMultiplicationSameWitnessMatrix

/-! The canonical first-factor multiplication successor step, assembled from
finite K derivations for the same old graph, suffix map, and row graph. This
is a first-factor relation theorem with its literal candidate and anchored-cut
antecedents; it does not by itself establish multiplication totality, the
second-factor PA multiplication axiom, or PA soundness. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationCanonicalSuccessorClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactForwardContextWithLex
open PASoundness.PAtoCompactMultiplicationForwardSharedContext
open PASoundness.PAtoCompactProductNewMatrixShape PASoundness.PAtoCompactProductNewLexShape
open PASoundness.PAtoCompactProductMatrixGraph64Intro
open PASoundness.PAtoCompactMultiplicationSameWitnessMatrix
open PASoundness.PAtoCompactMultiplicationCanonicalBaseStep
open PASoundness.PAtoCompactMultiplicationCanonicalFromMatrix
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The retained shared context proves the entire literal product matrix for
the same graph 64. The lex clause retained in the context is harmless here:
the imported matrix proof derives that clause from the shared context itself. -/
def matrix_from_retained_context : KDerivation
    (imp contextWithLex.encode matrix64.encode) := by
  have hp : KDerivation (imp contextWithLex.encode context.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [contextWithLex.encode]
    have h : Context Γ contextWithLex.encode := .head _ _
    have hb : Context Γ (both context.encode newLex.encode) := by
      simpa [contextWithLex, namedBoth, Formula.encode, Formula.not, both, neg] using h
    exact Context.conjunctionLeft hb
  have hm : KDerivation (imp context.encode matrix64.encode) := by
    simpa only [matrix64, canonicalBody, newMatrix] using matrix_from_context
  exact compose hp hm

/-- Finite K proof of the exact canonical first-factor product-successor
relation, with all candidate, source-successor and anchored-cut antecedents
spelled out in `canonical100`. No proof-data argument is supplied. -/
noncomputable def canonical_successor : KDerivation canonical100.encode :=
  canonical_from_matrix matrix_from_retained_context

theorem matrix_from_retained_context_certificate :
    theoremCode (certificate matrix_from_retained_context) =
      imp contextWithLex.encode matrix64.encode := certificate_correct _

theorem canonical_successor_certificate :
    theoremCode (certificate canonical_successor) = canonical100.encode := certificate_correct _
end PASoundness.PAtoCompactMultiplicationCanonicalSuccessorClosed
#print axioms PASoundness.PAtoCompactMultiplicationCanonicalSuccessorClosed.matrix_from_retained_context
#print axioms PASoundness.PAtoCompactMultiplicationCanonicalSuccessorClosed.canonical_successor
#print axioms PASoundness.PAtoCompactMultiplicationCanonicalSuccessorClosed.matrix_from_retained_context_certificate
#print axioms PASoundness.PAtoCompactMultiplicationCanonicalSuccessorClosed.canonical_successor_certificate
