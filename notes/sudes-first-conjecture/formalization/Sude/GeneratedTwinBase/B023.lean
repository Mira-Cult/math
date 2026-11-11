import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0053
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0082
import Sude.GeneratedFTT.N0085
import Sude.GeneratedFTT.N0086
import Sude.GeneratedFTT.N0087
import Sude.GeneratedFTT.N0089
import Sude.GeneratedFTT.N0091
import Sude.GeneratedFTT.N0102
import Sude.GeneratedFTT.N0107
import Sude.GeneratedFTT.N0132
import Sude.GeneratedFTT.N0137
import Sude.GeneratedFTT.N0141
import Sude.GeneratedFTT.N0150
import Sude.GeneratedTwinBase.M000
import Sude.GeneratedTwinBase.B021

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B023
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [12343, 12347, 12373, 12377, 12379, 12391, 12401, 12409, 12413, 12421, 12433, 12437, 12451, 12457, 12473, 12479, 12487, 12491, 12497, 12503, 12511, 12517, 12527, 12539, 12541, 12547, 12553, 12569, 12577, 12583, 12589, 12601, 12611, 12613, 12619, 12637, 12641, 12647, 12653, 12659, 12671, 12689, 12697, 12703, 12713, 12721, 12739, 12743, 12757, 12763, 12781, 12791, 12799, 12809, 12821, 12823, 12829, 12841, 12853, 12889, 12893, 12899, 12907, 12911]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_12343, by decide, by decide⟩,
    ⟨prime_12347, by decide, by decide⟩,
    ⟨prime_12373, by decide, by decide⟩,
    ⟨prime_12377, by decide, by decide⟩,
    ⟨prime_12379, by decide, by decide⟩,
    ⟨prime_12391, by decide, by decide⟩,
    ⟨prime_12401, by decide, by decide⟩,
    ⟨prime_12409, by decide, by decide⟩,
    ⟨prime_12413, by decide, by decide⟩,
    ⟨prime_12421, by decide, by decide⟩,
    ⟨prime_12433, by decide, by decide⟩,
    ⟨prime_12437, by decide, by decide⟩,
    ⟨prime_12451, by decide, by decide⟩,
    ⟨prime_12457, by decide, by decide⟩,
    ⟨prime_12473, by decide, by decide⟩,
    ⟨prime_12479, by decide, by decide⟩,
    ⟨prime_12487, by decide, by decide⟩,
    ⟨prime_12491, by decide, by decide⟩,
    ⟨prime_12497, by decide, by decide⟩,
    ⟨prime_12503, by decide, by decide⟩,
    ⟨prime_12511, by decide, by decide⟩,
    ⟨prime_12517, by decide, by decide⟩,
    ⟨prime_12527, by decide, by decide⟩,
    ⟨prime_12539, by decide, by decide⟩,
    ⟨prime_12541, by decide, by decide⟩,
    ⟨prime_12547, by decide, by decide⟩,
    ⟨prime_12553, by decide, by decide⟩,
    ⟨prime_12569, by decide, by decide⟩,
    ⟨prime_12577, by decide, by decide⟩,
    ⟨prime_12583, by decide, by decide⟩,
    ⟨prime_12589, by decide, by decide⟩,
    ⟨prime_12601, by decide, by decide⟩,
    ⟨prime_12611, by decide, by decide⟩,
    ⟨prime_12613, by decide, by decide⟩,
    ⟨prime_12619, by decide, by decide⟩,
    ⟨prime_12637, by decide, by decide⟩,
    ⟨prime_12641, by decide, by decide⟩,
    ⟨prime_12647, by decide, by decide⟩,
    ⟨prime_12653, by decide, by decide⟩,
    ⟨prime_12659, by decide, by decide⟩,
    ⟨prime_12671, by decide, by decide⟩,
    ⟨prime_12689, by decide, by decide⟩,
    ⟨prime_12697, by decide, by decide⟩,
    ⟨prime_12703, by decide, by decide⟩,
    ⟨prime_12713, by decide, by decide⟩,
    ⟨prime_12721, by decide, by decide⟩,
    ⟨prime_12739, by decide, by decide⟩,
    ⟨prime_12743, by decide, by decide⟩,
    ⟨prime_12757, by decide, by decide⟩,
    ⟨prime_12763, by decide, by decide⟩,
    ⟨prime_12781, by decide, by decide⟩,
    ⟨prime_12791, by decide, by decide⟩,
    ⟨prime_12799, by decide, by decide⟩,
    ⟨prime_12809, by decide, by decide⟩,
    ⟨prime_12821, by decide, by decide⟩,
    ⟨prime_12823, by decide, by decide⟩,
    ⟨prime_12829, by decide, by decide⟩,
    ⟨prime_12841, by decide, by decide⟩,
    ⟨prime_12853, by decide, by decide⟩,
    ⟨prime_12889, by decide, by decide⟩,
    ⟨prime_12893, by decide, by decide⟩,
    ⟨prime_12899, by decide, by decide⟩,
    ⟨prime_12907, by decide, by decide⟩,
    ⟨prime_12911, by decide, by decide⟩
  ⟩

end B023
end Sude.Lucas.Generated
