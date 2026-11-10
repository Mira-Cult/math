import PASoundness.PAtoCompactFilteredSubset
import PASoundness.PAtoCompactOrdinalAddition
import PASoundness.CompactQuantifiers

/-! Syntactic alignment between the proposed addition suffix clause and the
literal selector-8 filter graph. This is not an addition existence,
quotient-congruence, or PA proof-translation theorem. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionSuffixAlignment
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactOrdinalAddition

/-- The addition proposal's literal suffix clause is precisely the fixed-name
filter graph for the result 32 and cut 33. -/
theorem suffix_code : suffixFormula.encode = filterGraph 32 34 35 (neg (member 33 35)) := by
  rfl

end PASoundness.PAtoCompactAdditionSuffixAlignment

#print axioms PASoundness.PAtoCompactAdditionSuffixAlignment.suffix_code
