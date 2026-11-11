import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0078
import Sude.GeneratedFTT.N0080
import Sude.GeneratedFTT.N0088
import Sude.GeneratedFTT.N0091
import Sude.GeneratedFTT.N0098
import Sude.GeneratedFTT.N0110
import Sude.GeneratedFTT.N0111
import Sude.GeneratedFTT.N0115
import Sude.GeneratedFTT.N0116
import Sude.GeneratedFTT.N0123
import Sude.GeneratedFTT.N0125
import Sude.GeneratedFTT.N0141
import Sude.GeneratedFTT.N0143
import Sude.GeneratedFTT.N0146
import Sude.GeneratedFTT.N0150
import Sude.GeneratedTwinBase.M000
import Sude.GeneratedTwinBase.B026

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B028
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [15359, 15361, 15373, 15377, 15383, 15391, 15401, 15413, 15427, 15439, 15443, 15451, 15461, 15467, 15473, 15493, 15497, 15511, 15527, 15541, 15551, 15559, 15569, 15581, 15583, 15601, 15607, 15619, 15629, 15641, 15643, 15647, 15649, 15661, 15667, 15671, 15679, 15683, 15727, 15731, 15733, 15737, 15739, 15749, 15761, 15767, 15773, 15787, 15791, 15797, 15803, 15809, 15817, 15823, 15859, 15877, 15881, 15887, 15889, 15901, 15907, 15913, 15919, 15923]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_15359, by decide, by decide⟩,
    ⟨prime_15361, by decide, by decide⟩,
    ⟨prime_15373, by decide, by decide⟩,
    ⟨prime_15377, by decide, by decide⟩,
    ⟨prime_15383, by decide, by decide⟩,
    ⟨prime_15391, by decide, by decide⟩,
    ⟨prime_15401, by decide, by decide⟩,
    ⟨prime_15413, by decide, by decide⟩,
    ⟨prime_15427, by decide, by decide⟩,
    ⟨prime_15439, by decide, by decide⟩,
    ⟨prime_15443, by decide, by decide⟩,
    ⟨prime_15451, by decide, by decide⟩,
    ⟨prime_15461, by decide, by decide⟩,
    ⟨prime_15467, by decide, by decide⟩,
    ⟨prime_15473, by decide, by decide⟩,
    ⟨prime_15493, by decide, by decide⟩,
    ⟨prime_15497, by decide, by decide⟩,
    ⟨prime_15511, by decide, by decide⟩,
    ⟨prime_15527, by decide, by decide⟩,
    ⟨prime_15541, by decide, by decide⟩,
    ⟨prime_15551, by decide, by decide⟩,
    ⟨prime_15559, by decide, by decide⟩,
    ⟨prime_15569, by decide, by decide⟩,
    ⟨prime_15581, by decide, by decide⟩,
    ⟨prime_15583, by decide, by decide⟩,
    ⟨prime_15601, by decide, by decide⟩,
    ⟨prime_15607, by decide, by decide⟩,
    ⟨prime_15619, by decide, by decide⟩,
    ⟨prime_15629, by decide, by decide⟩,
    ⟨prime_15641, by decide, by decide⟩,
    ⟨prime_15643, by decide, by decide⟩,
    ⟨prime_15647, by decide, by decide⟩,
    ⟨prime_15649, by decide, by decide⟩,
    ⟨prime_15661, by decide, by decide⟩,
    ⟨prime_15667, by decide, by decide⟩,
    ⟨prime_15671, by decide, by decide⟩,
    ⟨prime_15679, by decide, by decide⟩,
    ⟨prime_15683, by decide, by decide⟩,
    ⟨prime_15727, by decide, by decide⟩,
    ⟨prime_15731, by decide, by decide⟩,
    ⟨prime_15733, by decide, by decide⟩,
    ⟨prime_15737, by decide, by decide⟩,
    ⟨prime_15739, by decide, by decide⟩,
    ⟨prime_15749, by decide, by decide⟩,
    ⟨prime_15761, by decide, by decide⟩,
    ⟨prime_15767, by decide, by decide⟩,
    ⟨prime_15773, by decide, by decide⟩,
    ⟨prime_15787, by decide, by decide⟩,
    ⟨prime_15791, by decide, by decide⟩,
    ⟨prime_15797, by decide, by decide⟩,
    ⟨prime_15803, by decide, by decide⟩,
    ⟨prime_15809, by decide, by decide⟩,
    ⟨prime_15817, by decide, by decide⟩,
    ⟨prime_15823, by decide, by decide⟩,
    ⟨prime_15859, by decide, by decide⟩,
    ⟨prime_15877, by decide, by decide⟩,
    ⟨prime_15881, by decide, by decide⟩,
    ⟨prime_15887, by decide, by decide⟩,
    ⟨prime_15889, by decide, by decide⟩,
    ⟨prime_15901, by decide, by decide⟩,
    ⟨prime_15907, by decide, by decide⟩,
    ⟨prime_15913, by decide, by decide⟩,
    ⟨prime_15919, by decide, by decide⟩,
    ⟨prime_15923, by decide, by decide⟩
  ⟩

end B028
end Sude.Lucas.Generated
