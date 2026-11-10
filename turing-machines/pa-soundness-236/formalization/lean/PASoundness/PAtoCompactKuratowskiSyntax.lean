import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactUnorderedPair

/-! Exact syntactic alignment between the quotient proposal's relational
Kuratowski pair and the already defined singleton and unordered-pair graph
formulas. This proves neither existence of a witness nor quotient properties.
Named bottom encodes literal `member 0 0`; the named free-name calculation is
not a general semantic claim about bottom in raw K models. -/
namespace PASoundness.PAtoCompactKuratowskiSyntax
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactSingleton
open PASoundness.PAtoCompactUnorderedPair PASoundness.PAtoCompactOrderIsomorphism

/-- The exact named formula is an existential singleton and unordered-pair
witness with a final unordered pair of those two witnesses. This identity is
syntactic and holds even when displayed names collide. The intended relational
reading requires inputs p,a,b distinct from binders 20,21,22. -/
theorem pair_formula_named (p a b : Nat) :
    pairFormula p a b = .ex 20 (.ex 21
      (namedBoth (namedSingleton a 20 22)
        (namedBoth (namedPair a b 21 22) (namedPair 20 21 p 22)))) := by
  rfl

/-- Literal compact code of the same formula; quantifiers and conjunctions
remain the exact K encodings. -/
theorem pair_formula_code (p a b : Nat) :
    (pairFormula p a b).encode =
      existsCode 20 (existsCode 21 (both (singletonCode a 20 22)
        (both (pairCode a b 21 22) (pairCode 20 21 p 22)))) := by
  rw [pair_formula_named]
  rfl

end PASoundness.PAtoCompactKuratowskiSyntax

#print axioms PASoundness.PAtoCompactKuratowskiSyntax.pair_formula_named
#print axioms PASoundness.PAtoCompactKuratowskiSyntax.pair_formula_code
