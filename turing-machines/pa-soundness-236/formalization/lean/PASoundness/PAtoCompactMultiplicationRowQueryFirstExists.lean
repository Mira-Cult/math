import PASoundness.PAtoCompactMultiplicationRowQueryFirst

/-! Eliminate the two explicit nested-edge witnesses from the first queried
new-row case. Membership in the row branch is part of the existential
hypothesis; this does not establish the graph's old/new split, row collection,
or multiplication totality. -/
namespace PASoundness.PAtoCompactMultiplicationRowQueryFirstExists
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactMultiplicationRowQueryFirst
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- One queried edge has an inner pair 18 and outer edge 63 satisfying
both its pair formulas and the explicit new-row witness branch. -/
def queriedNewRow : Formula := .ex 18 (.ex 63
  (namedBoth queryPairs (replace 9 63 rowWitness)))

/-- Every such new-row query has the specified major, a valid row index,
and the corresponding edge of the supplied suffix graph. -/
def query_exists_elim : KDerivation (imp queriedNewRow.encode queryResult.encode) := by
  let B := namedBoth queryPairs (replace 9 63 rowWitness)
  have hpoint : KDerivation (imp B.encode queryResult.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    have h : Context [B.encode] B.encode := .head [] _
    have h' : Context [B.encode] (both queryPairs.encode (replace 9 63 rowWitness).encode) := by
      simpa [B,namedBoth,Formula.not,Formula.encode,both,neg] using h
    exact .mp (Context.conjunctionRight h') (.mp (Context.conjunctionLeft h') (.closed row_query))
  have h63 : KDerivation (imp (existsCode 63 B.encode) queryResult.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.existsElim (queryResult.vacuity 63 (by decide))
      (.closed (.generalize 63 hpoint)) (.head [] _)
  have h18 : KDerivation (imp (existsCode 18 (existsCode 63 B.encode)) queryResult.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.existsElim (queryResult.vacuity 18 (by decide))
      (.closed (.generalize 18 h63)) (.head [] _)
  simpa [queriedNewRow,B,Formula.encode] using h18

theorem query_exists_elim_certificate : theoremCode (certificate query_exists_elim) =
    imp queriedNewRow.encode queryResult.encode := certificate_correct _
end PASoundness.PAtoCompactMultiplicationRowQueryFirstExists
#print axioms PASoundness.PAtoCompactMultiplicationRowQueryFirstExists.query_exists_elim
#print axioms PASoundness.PAtoCompactMultiplicationRowQueryFirstExists.query_exists_elim_certificate
