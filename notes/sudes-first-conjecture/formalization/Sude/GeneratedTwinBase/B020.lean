import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0053
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0082
import Sude.GeneratedFTT.N0084
import Sude.GeneratedFTT.N0085
import Sude.GeneratedFTT.N0089
import Sude.GeneratedFTT.N0094
import Sude.GeneratedFTT.N0096
import Sude.GeneratedFTT.N0103
import Sude.GeneratedFTT.N0105
import Sude.GeneratedFTT.N0118
import Sude.GeneratedFTT.N0123
import Sude.GeneratedFTT.N0126
import Sude.GeneratedFTT.N0136
import Sude.GeneratedFTT.N0144
import Sude.GeneratedTwinBase.M000
import Sude.GeneratedTwinBase.B018

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B020
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [10477, 10487, 10499, 10501, 10513, 10529, 10531, 10559, 10567, 10589, 10597, 10601, 10607, 10613, 10627, 10631, 10639, 10651, 10657, 10663, 10667, 10687, 10691, 10709, 10711, 10723, 10729, 10733, 10739, 10753, 10771, 10781, 10789, 10799, 10831, 10837, 10847, 10853, 10859, 10861, 10867, 10883, 10889, 10891, 10903, 10909, 10937, 10939, 10949, 10957, 10973, 10979, 10987, 10993, 11003, 11027, 11047, 11057, 11059, 11069, 11071, 11083, 11087, 11093]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_10477, by decide, by decide⟩,
    ⟨prime_10487, by decide, by decide⟩,
    ⟨prime_10499, by decide, by decide⟩,
    ⟨prime_10501, by decide, by decide⟩,
    ⟨prime_10513, by decide, by decide⟩,
    ⟨prime_10529, by decide, by decide⟩,
    ⟨prime_10531, by decide, by decide⟩,
    ⟨prime_10559, by decide, by decide⟩,
    ⟨prime_10567, by decide, by decide⟩,
    ⟨prime_10589, by decide, by decide⟩,
    ⟨prime_10597, by decide, by decide⟩,
    ⟨prime_10601, by decide, by decide⟩,
    ⟨prime_10607, by decide, by decide⟩,
    ⟨prime_10613, by decide, by decide⟩,
    ⟨prime_10627, by decide, by decide⟩,
    ⟨prime_10631, by decide, by decide⟩,
    ⟨prime_10639, by decide, by decide⟩,
    ⟨prime_10651, by decide, by decide⟩,
    ⟨prime_10657, by decide, by decide⟩,
    ⟨prime_10663, by decide, by decide⟩,
    ⟨prime_10667, by decide, by decide⟩,
    ⟨prime_10687, by decide, by decide⟩,
    ⟨prime_10691, by decide, by decide⟩,
    ⟨prime_10709, by decide, by decide⟩,
    ⟨prime_10711, by decide, by decide⟩,
    ⟨prime_10723, by decide, by decide⟩,
    ⟨prime_10729, by decide, by decide⟩,
    ⟨prime_10733, by decide, by decide⟩,
    ⟨prime_10739, by decide, by decide⟩,
    ⟨prime_10753, by decide, by decide⟩,
    ⟨prime_10771, by decide, by decide⟩,
    ⟨prime_10781, by decide, by decide⟩,
    ⟨prime_10789, by decide, by decide⟩,
    ⟨prime_10799, by decide, by decide⟩,
    ⟨prime_10831, by decide, by decide⟩,
    ⟨prime_10837, by decide, by decide⟩,
    ⟨prime_10847, by decide, by decide⟩,
    ⟨prime_10853, by decide, by decide⟩,
    ⟨prime_10859, by decide, by decide⟩,
    ⟨prime_10861, by decide, by decide⟩,
    ⟨prime_10867, by decide, by decide⟩,
    ⟨prime_10883, by decide, by decide⟩,
    ⟨prime_10889, by decide, by decide⟩,
    ⟨prime_10891, by decide, by decide⟩,
    ⟨prime_10903, by decide, by decide⟩,
    ⟨prime_10909, by decide, by decide⟩,
    ⟨prime_10937, by decide, by decide⟩,
    ⟨prime_10939, by decide, by decide⟩,
    ⟨prime_10949, by decide, by decide⟩,
    ⟨prime_10957, by decide, by decide⟩,
    ⟨prime_10973, by decide, by decide⟩,
    ⟨prime_10979, by decide, by decide⟩,
    ⟨prime_10987, by decide, by decide⟩,
    ⟨prime_10993, by decide, by decide⟩,
    ⟨prime_11003, by decide, by decide⟩,
    ⟨prime_11027, by decide, by decide⟩,
    ⟨prime_11047, by decide, by decide⟩,
    ⟨prime_11057, by decide, by decide⟩,
    ⟨prime_11059, by decide, by decide⟩,
    ⟨prime_11069, by decide, by decide⟩,
    ⟨prime_11071, by decide, by decide⟩,
    ⟨prime_11083, by decide, by decide⟩,
    ⟨prime_11087, by decide, by decide⟩,
    ⟨prime_11093, by decide, by decide⟩
  ⟩

end B020
end Sude.Lucas.Generated
