import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0078
import Sude.GeneratedFTT.N0100
import Sude.GeneratedFTT.N0103
import Sude.GeneratedTwinBase.B009

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B011
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [5333, 5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_5333, by decide, by decide⟩,
    ⟨prime_5347, by decide, by decide⟩,
    ⟨prime_5351, by decide, by decide⟩,
    ⟨prime_5381, by decide, by decide⟩,
    ⟨prime_5387, by decide, by decide⟩,
    ⟨prime_5393, by decide, by decide⟩,
    ⟨prime_5399, by decide, by decide⟩,
    ⟨prime_5407, by decide, by decide⟩,
    ⟨prime_5413, by decide, by decide⟩,
    ⟨prime_5417, by decide, by decide⟩,
    ⟨prime_5419, by decide, by decide⟩,
    ⟨prime_5431, by decide, by decide⟩,
    ⟨prime_5437, by decide, by decide⟩,
    ⟨prime_5441, by decide, by decide⟩,
    ⟨prime_5443, by decide, by decide⟩,
    ⟨prime_5449, by decide, by decide⟩,
    ⟨prime_5471, by decide, by decide⟩,
    ⟨prime_5477, by decide, by decide⟩,
    ⟨prime_5479, by decide, by decide⟩,
    ⟨prime_5483, by decide, by decide⟩,
    ⟨prime_5501, by decide, by decide⟩,
    ⟨prime_5503, by decide, by decide⟩,
    ⟨prime_5507, by decide, by decide⟩,
    ⟨prime_5519, by decide, by decide⟩,
    ⟨prime_5521, by decide, by decide⟩,
    ⟨prime_5527, by decide, by decide⟩,
    ⟨prime_5531, by decide, by decide⟩,
    ⟨prime_5557, by decide, by decide⟩,
    ⟨prime_5563, by decide, by decide⟩,
    ⟨prime_5569, by decide, by decide⟩,
    ⟨prime_5573, by decide, by decide⟩,
    ⟨prime_5581, by decide, by decide⟩,
    ⟨prime_5591, by decide, by decide⟩,
    ⟨prime_5623, by decide, by decide⟩,
    ⟨prime_5639, by decide, by decide⟩,
    ⟨prime_5641, by decide, by decide⟩,
    ⟨prime_5647, by decide, by decide⟩,
    ⟨prime_5651, by decide, by decide⟩,
    ⟨prime_5653, by decide, by decide⟩,
    ⟨prime_5657, by decide, by decide⟩,
    ⟨prime_5659, by decide, by decide⟩,
    ⟨prime_5669, by decide, by decide⟩,
    ⟨prime_5683, by decide, by decide⟩,
    ⟨prime_5689, by decide, by decide⟩,
    ⟨prime_5693, by decide, by decide⟩,
    ⟨prime_5701, by decide, by decide⟩,
    ⟨prime_5711, by decide, by decide⟩,
    ⟨prime_5717, by decide, by decide⟩,
    ⟨prime_5737, by decide, by decide⟩,
    ⟨prime_5741, by decide, by decide⟩,
    ⟨prime_5743, by decide, by decide⟩,
    ⟨prime_5749, by decide, by decide⟩,
    ⟨prime_5779, by decide, by decide⟩,
    ⟨prime_5783, by decide, by decide⟩,
    ⟨prime_5791, by decide, by decide⟩,
    ⟨prime_5801, by decide, by decide⟩,
    ⟨prime_5807, by decide, by decide⟩,
    ⟨prime_5813, by decide, by decide⟩,
    ⟨prime_5821, by decide, by decide⟩,
    ⟨prime_5827, by decide, by decide⟩,
    ⟨prime_5839, by decide, by decide⟩,
    ⟨prime_5843, by decide, by decide⟩,
    ⟨prime_5849, by decide, by decide⟩,
    ⟨prime_5851, by decide, by decide⟩
  ⟩

end B011
end Sude.Lucas.Generated
