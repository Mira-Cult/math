import PASoundness.PAtoCompactSeededSpanCutEquivalenceFromEquivalences
import PASoundness.PAtoCompactOrdinalAddition

/-! Record the literal connection between the two supplied cut isomorphisms
and the equivalence conjunct in the addition relation. -/
namespace PASoundness.PAtoCompactSeededSpanAdditionCutAlignment

open PASoundness.CompactNamed PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactSeededSpanCutEquivalenceFromEquivalences

set_option maxRecDepth 262144
set_option maxHeartbeats 0

/-- The first supplied cut equivalence is the addition equivalence at 28,40. -/
theorem first_cut_alignment : firstEquivalence = equivAt 28 40 := by decide

/-- The second supplied cut equivalence is the addition equivalence at 28,41. -/
theorem second_cut_alignment : secondEquivalence = equivAt 28 41 := by decide

end PASoundness.PAtoCompactSeededSpanAdditionCutAlignment

#print axioms PASoundness.PAtoCompactSeededSpanAdditionCutAlignment.first_cut_alignment
#print axioms PASoundness.PAtoCompactSeededSpanAdditionCutAlignment.second_cut_alignment
