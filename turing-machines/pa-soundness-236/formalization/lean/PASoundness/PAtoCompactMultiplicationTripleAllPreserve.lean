import PASoundness.PAtoCompactMultiplicationTripleAdjoinPreserve

/-! An adjoined graph preserves every existing product-style triple. This
quantifies the fixed-label K proof; it does not construct an entire new row
or a product graph. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationTripleAllPreserve
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactMultiplicationTripleAdjoinPreserve
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Every triple of the old graph remains a triple of the graph formed by
adjoining the supplied point. The label-bound variables 3, 4, and 5 range
independently in K. -/
def all_triples_preserved : KDerivation (imp (adjoinCode 6 12 9 16)
    (allCode 3 (allCode 4 (allCode 5
      (imp (tripleAt 6 3 4 5).encode (tripleAt 9 3 4 5).encode))))) := by
  let A := adjoinCode 6 12 9 16
  let F := imp (tripleAt 6 3 4 5).encode (tripleAt 9 3 4 5).encode
  let af : Formula := namedAdjoin 6 12 9 16
  have vac (x : Nat) (hx : x ∈ [3,4,5]) : KDerivation (imp A (allCode x A)) := by
    have h : x ∉ af.names := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide
    have hv := af.vacuity x h
    simpa [af,A,adjoinCode,namedAdjoin,namedBoth,namedEither,Formula.encode,
      CompactProof.both,CompactProof.neg,CompactDerivations.either] using hv
  have h : Context [A] F := .mp (.head [] A) (.closed triple_preserved)
  have h5 := generalizeOne 5 (vac 5 (by decide)) h
  have h4 := generalizeOne 4 (vac 4 (by decide)) h5
  have h3 := generalizeOne 3 (vac 3 (by decide)) h4
  exact Context.closeEmpty (Context.deduction h3)

theorem all_triples_preserved_certificate :
    theoremCode (certificate all_triples_preserved) =
      imp (adjoinCode 6 12 9 16)
        (allCode 3 (allCode 4 (allCode 5
          (imp (tripleAt 6 3 4 5).encode (tripleAt 9 3 4 5).encode)))) :=
  certificate_correct all_triples_preserved
end PASoundness.PAtoCompactMultiplicationTripleAllPreserve
#print axioms PASoundness.PAtoCompactMultiplicationTripleAllPreserve.all_triples_preserved
#print axioms PASoundness.PAtoCompactMultiplicationTripleAllPreserve.all_triples_preserved_certificate
