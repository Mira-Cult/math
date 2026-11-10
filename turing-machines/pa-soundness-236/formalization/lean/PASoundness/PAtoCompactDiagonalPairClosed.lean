import PASoundness.PAtoCompactDiagonalPair
import PASoundness.PAtoCompactKuratowskiExists

/-! An individual diagonal pair exists in K. This does not construct an
identity graph, establish a quotient, or interpret PA. -/
namespace PASoundness.PAtoCompactDiagonalPairClosed
open PASoundness.CompactProof PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactDiagonalPair

/-- K proves an individual pair with both endpoints read from name 2. -/
def diagonal_pair_exists : KDerivation
    (existsCode 19 (pairFormula 19 2 2).encode) :=
  diagonal_from_pair PASoundness.PAtoCompactKuratowskiExists.pair_exists

theorem diagonal_pair_exists_certificate :
    theoremCode (certificate diagonal_pair_exists) =
      existsCode 19 (pairFormula 19 2 2).encode := certificate_correct diagonal_pair_exists

end PASoundness.PAtoCompactDiagonalPairClosed

#print axioms PASoundness.PAtoCompactDiagonalPairClosed.diagonal_pair_exists
#print axioms PASoundness.PAtoCompactDiagonalPairClosed.diagonal_pair_exists_certificate
