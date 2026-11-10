import PASoundness.PAtoCompactMultiplicationRowQuerySecond

/-! Eliminate the nested-edge witnesses from the second queried new-row case.
The new-row branch is part of the existential hypothesis; this does not
establish the graph's old/new split, row collection, or multiplication
totality. -/
namespace PASoundness.PAtoCompactMultiplicationRowQuerySecondExists
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactMultiplicationRowQuerySecond
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Queried product coordinates 7,8,9 have a nested edge in the new row. -/
def queriedNewRowSecond : Formula := .ex 18 (.ex 63
  (namedBoth queryPairsSecond (replace 9 63 rowWitness)))

/-- This explicit branch supplies the second queried major, minor-domain
membership and suffix-map edge. -/
def query_second_exists_elim : KDerivation
    (imp queriedNewRowSecond.encode queryResultSecond.encode) := by
  let B := namedBoth queryPairsSecond (replace 9 63 rowWitness)
  have hpoint : KDerivation (imp B.encode queryResultSecond.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    have h : Context [B.encode] B.encode := .head [] _
    have h' : Context [B.encode]
        (both queryPairsSecond.encode (replace 9 63 rowWitness).encode) := by
      simpa [B,namedBoth,Formula.not,Formula.encode,both,neg] using h
    exact .mp (Context.conjunctionRight h') (.mp (Context.conjunctionLeft h') (.closed row_query_second))
  have h63 : KDerivation (imp (existsCode 63 B.encode) queryResultSecond.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.existsElim (queryResultSecond.vacuity 63 (by decide))
      (.closed (.generalize 63 hpoint)) (.head [] _)
  have h18 : KDerivation (imp (existsCode 18 (existsCode 63 B.encode)) queryResultSecond.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.existsElim (queryResultSecond.vacuity 18 (by decide))
      (.closed (.generalize 18 h63)) (.head [] _)
  simpa [queriedNewRowSecond,B,Formula.encode] using h18

theorem query_second_exists_elim_certificate : theoremCode (certificate query_second_exists_elim) =
    imp queriedNewRowSecond.encode queryResultSecond.encode := certificate_correct _
end PASoundness.PAtoCompactMultiplicationRowQuerySecondExists
#print axioms PASoundness.PAtoCompactMultiplicationRowQuerySecondExists.query_second_exists_elim
#print axioms PASoundness.PAtoCompactMultiplicationRowQuerySecondExists.query_second_exists_elim_certificate
