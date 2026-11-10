import PASoundness.PAtoCompactMultiplicationLexSharedContext
import PASoundness.PAtoCompactFixedFirstRowGraph64
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.PAtoCompactAdjunction

/-! A single named K context for the product-successor matrix obligations.
It retains the exact old graph 10, suffix graph 6, row graph 64, candidate and
cut hypotheses, and raw successor. It asserts none of these hypotheses and
does not itself construct a product or prove multiplication totality. -/
namespace PASoundness.PAtoCompactMultiplicationForwardSharedContext
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactMultiplicationLexSharedContext
open PASoundness.PAtoCompactFixedFirstRowGraph64 PASoundness.PAtoCompactFixedFirstRowSuffixTarget40
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactFreeVacuity
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- All four fields refer to the same free graph witnesses. -/
def context : Formula := namedBoth sharedPremise
  (namedBoth mapBijection40 (namedBoth rowBody64 (namedSuccessor 30 38 39)))

/-- The queried source labels are free-fresh despite appearing as internal
binders of some constituent formulas. -/
theorem context_free : context.free = {6,10,30,31,32,38,40,45,64} := by decide

def context_vacuity3 : KDerivation (imp context.encode (allCode 3 context.encode)) :=
  free_vacuity 3 context (by rw [context_free]; decide)
def context_vacuity4 : KDerivation (imp context.encode (allCode 4 context.encode)) :=
  free_vacuity 4 context (by rw [context_free]; decide)

/-- Literal K projections; no graph or arithmetic witness is constructed. -/
def project_shared : KDerivation (imp context.encode sharedPremise.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  have h : Context [context.encode] (both sharedPremise.encode
      (both mapBijection40.encode (both rowBody64.encode (successorCode 30 38 39)))) := by
    have h : Context [context.encode] context.encode := .head [] _
    simpa [context,namedBoth,namedSuccessor,namedSuccessorBody,namedEither,Formula.not,
      Formula.encode,both,neg,either,successorCode] using h
  exact Context.conjunctionLeft h

def project_map : KDerivation (imp context.encode mapBijection40.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  have h : Context [context.encode] (both sharedPremise.encode
      (both mapBijection40.encode (both rowBody64.encode (successorCode 30 38 39)))) := by
    have h : Context [context.encode] context.encode := .head [] _
    simpa [context,namedBoth,namedSuccessor,namedSuccessorBody,namedEither,Formula.not,
      Formula.encode,both,neg,either,successorCode] using h
  exact Context.conjunctionLeft (Context.conjunctionRight h)

def project_row : KDerivation (imp context.encode rowBody64.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  have h : Context [context.encode] (both sharedPremise.encode
      (both mapBijection40.encode (both rowBody64.encode (successorCode 30 38 39)))) := by
    have h : Context [context.encode] context.encode := .head [] _
    simpa [context,namedBoth,namedSuccessor,namedSuccessorBody,namedEither,Formula.not,
      Formula.encode,both,neg,either,successorCode] using h
  exact Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight h))

def project_successor : KDerivation (imp context.encode (successorCode 30 38 39)) := by
  apply Context.closeEmpty
  apply Context.deduction
  have h : Context [context.encode] (both sharedPremise.encode
      (both mapBijection40.encode (both rowBody64.encode (successorCode 30 38 39)))) := by
    have h : Context [context.encode] context.encode := .head [] _
    simpa [context,namedBoth,namedSuccessor,namedSuccessorBody,namedEither,Formula.not,
      Formula.encode,both,neg,either,successorCode] using h
  exact Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight h))

end PASoundness.PAtoCompactMultiplicationForwardSharedContext
#print axioms PASoundness.PAtoCompactMultiplicationForwardSharedContext.context_free
#print axioms PASoundness.PAtoCompactMultiplicationForwardSharedContext.context_vacuity3
#print axioms PASoundness.PAtoCompactMultiplicationForwardSharedContext.context_vacuity4
#print axioms PASoundness.PAtoCompactMultiplicationForwardSharedContext.project_shared
#print axioms PASoundness.PAtoCompactMultiplicationForwardSharedContext.project_map
#print axioms PASoundness.PAtoCompactMultiplicationForwardSharedContext.project_row
#print axioms PASoundness.PAtoCompactMultiplicationForwardSharedContext.project_successor
