import PASoundness.PAtoCompactPairAuto
import PASoundness.PAtoCompactPairRepeated

/-! Unconditional K unordered-pair existence for all endpoint names, with
computed auxiliary names. The witness is a represented pair graph; no
uniqueness of representatives, graph collection, quotient or arithmetic
interpretation is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPairAll
open PASoundness.CompactProof PASoundness.PAtoCompactSingletonSelector
open PASoundness.PAtoCompactUnorderedPair PASoundness.PAtoCompactPairFresh
open PASoundness.PAtoCompactPairAuto PASoundness.PAtoCompactPairRepeated

/-- Capture-safe test label selected by endpoint-name collision. -/
def testName (a b : Nat) : Nat :=
  if a = b then singletonPredicate a (a+1) + 1 else pairTest a b

/-- Output witness label selected by endpoint-name collision. -/
def witnessName (a b : Nat) : Nat :=
  if a = b then singletonPredicate a (a+1) + 2 else pairName a b

/-- K constructs an unordered pair for every choice of endpoint names. -/
def pair_exists (a b : Nat) : KDerivation
    (existsCode (witnessName a b) (pairCode a b (witnessName a b) (testName a b))) := by
  by_cases h : a = b
  · subst b
    simpa [testName,witnessName] using repeated_pair_exists a
  · simpa [testName,witnessName,h] using distinct_pair_exists a b h

theorem pair_exists_certificate (a b : Nat) :
    theoremCode (certificate (pair_exists a b)) =
      existsCode (witnessName a b) (pairCode a b (witnessName a b) (testName a b)) :=
  certificate_correct (pair_exists a b)

end PASoundness.PAtoCompactPairAll

#print axioms PASoundness.PAtoCompactPairAll.pair_exists
#print axioms PASoundness.PAtoCompactPairAll.pair_exists_certificate
