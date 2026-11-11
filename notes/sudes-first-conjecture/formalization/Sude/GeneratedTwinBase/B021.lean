import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0084
import Sude.GeneratedFTT.N0087
import Sude.GeneratedFTT.N0090
import Sude.GeneratedFTT.N0093
import Sude.GeneratedFTT.N0095
import Sude.GeneratedFTT.N0097
import Sude.GeneratedFTT.N0098
import Sude.GeneratedFTT.N0099
import Sude.GeneratedFTT.N0100
import Sude.GeneratedFTT.N0107
import Sude.GeneratedFTT.N0112
import Sude.GeneratedFTT.N0123
import Sude.GeneratedFTT.N0125
import Sude.GeneratedFTT.N0135
import Sude.GeneratedFTT.N0148
import Sude.GeneratedTwinBase.M000
import Sude.GeneratedTwinBase.B019

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B021
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [11113, 11117, 11119, 11131, 11149, 11159, 11161, 11171, 11173, 11177, 11197, 11213, 11239, 11243, 11251, 11257, 11261, 11273, 11279, 11287, 11299, 11311, 11317, 11321, 11329, 11351, 11353, 11369, 11383, 11393, 11399, 11411, 11423, 11437, 11443, 11447, 11467, 11471, 11483, 11489, 11491, 11497, 11503, 11519, 11527, 11549, 11551, 11579, 11587, 11593, 11597, 11617, 11621, 11633, 11657, 11677, 11681, 11689, 11699, 11701, 11717, 11719, 11731, 11743]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_11113, by decide, by decide⟩,
    ⟨prime_11117, by decide, by decide⟩,
    ⟨prime_11119, by decide, by decide⟩,
    ⟨prime_11131, by decide, by decide⟩,
    ⟨prime_11149, by decide, by decide⟩,
    ⟨prime_11159, by decide, by decide⟩,
    ⟨prime_11161, by decide, by decide⟩,
    ⟨prime_11171, by decide, by decide⟩,
    ⟨prime_11173, by decide, by decide⟩,
    ⟨prime_11177, by decide, by decide⟩,
    ⟨prime_11197, by decide, by decide⟩,
    ⟨prime_11213, by decide, by decide⟩,
    ⟨prime_11239, by decide, by decide⟩,
    ⟨prime_11243, by decide, by decide⟩,
    ⟨prime_11251, by decide, by decide⟩,
    ⟨prime_11257, by decide, by decide⟩,
    ⟨prime_11261, by decide, by decide⟩,
    ⟨prime_11273, by decide, by decide⟩,
    ⟨prime_11279, by decide, by decide⟩,
    ⟨prime_11287, by decide, by decide⟩,
    ⟨prime_11299, by decide, by decide⟩,
    ⟨prime_11311, by decide, by decide⟩,
    ⟨prime_11317, by decide, by decide⟩,
    ⟨prime_11321, by decide, by decide⟩,
    ⟨prime_11329, by decide, by decide⟩,
    ⟨prime_11351, by decide, by decide⟩,
    ⟨prime_11353, by decide, by decide⟩,
    ⟨prime_11369, by decide, by decide⟩,
    ⟨prime_11383, by decide, by decide⟩,
    ⟨prime_11393, by decide, by decide⟩,
    ⟨prime_11399, by decide, by decide⟩,
    ⟨prime_11411, by decide, by decide⟩,
    ⟨prime_11423, by decide, by decide⟩,
    ⟨prime_11437, by decide, by decide⟩,
    ⟨prime_11443, by decide, by decide⟩,
    ⟨prime_11447, by decide, by decide⟩,
    ⟨prime_11467, by decide, by decide⟩,
    ⟨prime_11471, by decide, by decide⟩,
    ⟨prime_11483, by decide, by decide⟩,
    ⟨prime_11489, by decide, by decide⟩,
    ⟨prime_11491, by decide, by decide⟩,
    ⟨prime_11497, by decide, by decide⟩,
    ⟨prime_11503, by decide, by decide⟩,
    ⟨prime_11519, by decide, by decide⟩,
    ⟨prime_11527, by decide, by decide⟩,
    ⟨prime_11549, by decide, by decide⟩,
    ⟨prime_11551, by decide, by decide⟩,
    ⟨prime_11579, by decide, by decide⟩,
    ⟨prime_11587, by decide, by decide⟩,
    ⟨prime_11593, by decide, by decide⟩,
    ⟨prime_11597, by decide, by decide⟩,
    ⟨prime_11617, by decide, by decide⟩,
    ⟨prime_11621, by decide, by decide⟩,
    ⟨prime_11633, by decide, by decide⟩,
    ⟨prime_11657, by decide, by decide⟩,
    ⟨prime_11677, by decide, by decide⟩,
    ⟨prime_11681, by decide, by decide⟩,
    ⟨prime_11689, by decide, by decide⟩,
    ⟨prime_11699, by decide, by decide⟩,
    ⟨prime_11701, by decide, by decide⟩,
    ⟨prime_11717, by decide, by decide⟩,
    ⟨prime_11719, by decide, by decide⟩,
    ⟨prime_11731, by decide, by decide⟩,
    ⟨prime_11743, by decide, by decide⟩
  ⟩

end B021
end Sude.Lucas.Generated
