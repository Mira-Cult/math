import PASoundness.PAtoCompactMultiplicationSingleTripleExtension
import PASoundness.PAtoCompactMultiplicationTripleAllPreserve

/-! K constructs a graph obtained by adjoining one explicitly represented
product-style triple, and that same graph retains every old triple. This is
one extension point, not collection of a product row, multiplication totality
or PA proof transport. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationSingleTripleRetained
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactMultiplicationSingleTripleExtension
open PASoundness.PAtoCompactMultiplicationTripleAllPreserve
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private def P := (pairFormula 11 30 31).encode
private def Q := (pairFormula 12 11 32).encode
private def A := adjoinCode 6 12 9 16
private def T := (PAtoCompactMultiplicationSingleTripleExtension.tripleAt 9 30 31 32).encode
/-- The same extended graph preserves all prior multiplication-style edges. -/
def oldTriplesRetained : Nat := allCode 3 (allCode 4 (allCode 5 (imp
  (PAtoCompactMultiplicationTripleAdjoinPreserve.tripleAt 6 3 4 5).encode
  (PAtoCompactMultiplicationTripleAdjoinPreserve.tripleAt 9 3 4 5).encode)))

private def enrich : KDerivation (imp (both A T) (both A (both T oldTriplesRetained))) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [both A T]
  have h : Context Γ (both A T) := .head [] _
  have ha := Context.conjunctionLeft h
  have ht := Context.conjunctionRight h
  have hr : Context Γ oldTriplesRetained := .mp ha (.closed all_triples_preserved)
  exact Context.conjunctionIntro ha (Context.conjunctionIntro ht hr)

private def mapSecond : KDerivation
    (imp (both Q (existsCode 9 (both A T)))
      (both Q (existsCode 9 (both A (both T oldTriplesRetained))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [both Q (existsCode 9 (both A T))]
  have h : Context Γ (both Q (existsCode 9 (both A T))) := .head [] _
  exact Context.conjunctionIntro (Context.conjunctionLeft h)
    (.mp (Context.conjunctionRight h) (.closed (existsCongr 9 enrich)))

private def mapFirst : KDerivation
    (imp (both P (existsCode 12 (both Q (existsCode 9 (both A T)))))
      (both P (existsCode 12 (both Q (existsCode 9 (both A (both T oldTriplesRetained))))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [both P (existsCode 12 (both Q (existsCode 9 (both A T))))]
  have h : Context Γ (both P (existsCode 12 (both Q (existsCode 9 (both A T))))) := .head [] _
  exact Context.conjunctionIntro (Context.conjunctionLeft h)
    (.mp (Context.conjunctionRight h) (.closed (existsCongr 12 mapSecond)))

/-- A single graph extension contains the requested new triple while retaining
every old triple. The two nested-pair witnesses and the graph are constructed
inside K; their labels are existentially bound and input values may alias. -/
def single_triple_extension_retaining_old : KDerivation (existsCode 11
    (both (pairFormula 11 30 31).encode (existsCode 12
      (both (pairFormula 12 11 32).encode (existsCode 9
        (both (adjoinCode 6 12 9 16)
          (both (PAtoCompactMultiplicationSingleTripleExtension.tripleAt 9 30 31 32).encode
            oldTriplesRetained))))))) := by
  have he : KDerivation (existsCode 11 (both P (existsCode 12 (both Q (existsCode 9 (both A T)))))) :=
    single_triple_extension_exists
  exact .mp he (existsCongr 11 mapFirst)

theorem single_triple_extension_retaining_old_certificate :
    theoremCode (certificate single_triple_extension_retaining_old) = existsCode 11
      (both (pairFormula 11 30 31).encode (existsCode 12
        (both (pairFormula 12 11 32).encode (existsCode 9
          (both (adjoinCode 6 12 9 16)
            (both (PAtoCompactMultiplicationSingleTripleExtension.tripleAt 9 30 31 32).encode
              oldTriplesRetained)))))) := certificate_correct single_triple_extension_retaining_old
end PASoundness.PAtoCompactMultiplicationSingleTripleRetained
#print axioms PASoundness.PAtoCompactMultiplicationSingleTripleRetained.single_triple_extension_retaining_old
#print axioms PASoundness.PAtoCompactMultiplicationSingleTripleRetained.single_triple_extension_retaining_old_certificate
