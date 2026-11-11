import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0078
import Sude.GeneratedFTT.N0080
import Sude.GeneratedFTT.N0083
import Sude.GeneratedFTT.N0087
import Sude.GeneratedFTT.N0091
import Sude.GeneratedFTT.N0092
import Sude.GeneratedFTT.N0098
import Sude.GeneratedFTT.N0108
import Sude.GeneratedFTT.N0118
import Sude.GeneratedFTT.N0142
import Sude.GeneratedFTT.N0144
import Sude.GeneratedFTT.N0150
import Sude.GeneratedTwinBase.M002
import Sude.GeneratedTwinBase.B043

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B045
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [26227, 26237, 26249, 26251, 26261, 26263, 26267, 26293, 26297, 26309, 26317, 26321, 26339, 26347, 26357, 26371, 26387, 26393, 26399, 26407, 26417, 26423, 26431, 26437, 26449, 26459, 26479, 26489, 26497, 26501, 26513, 26539, 26557, 26561, 26573, 26591, 26597, 26627, 26633, 26641, 26647, 26669, 26681, 26683, 26687, 26693, 26699, 26701, 26711, 26713, 26717, 26723, 26729, 26731, 26737, 26759, 26777, 26783, 26801, 26813, 26821, 26833, 26839, 26849]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_26227, by decide, by decide⟩,
    ⟨prime_26237, by decide, by decide⟩,
    ⟨prime_26249, by decide, by decide⟩,
    ⟨prime_26251, by decide, by decide⟩,
    ⟨prime_26261, by decide, by decide⟩,
    ⟨prime_26263, by decide, by decide⟩,
    ⟨prime_26267, by decide, by decide⟩,
    ⟨prime_26293, by decide, by decide⟩,
    ⟨prime_26297, by decide, by decide⟩,
    ⟨prime_26309, by decide, by decide⟩,
    ⟨prime_26317, by decide, by decide⟩,
    ⟨prime_26321, by decide, by decide⟩,
    ⟨prime_26339, by decide, by decide⟩,
    ⟨prime_26347, by decide, by decide⟩,
    ⟨prime_26357, by decide, by decide⟩,
    ⟨prime_26371, by decide, by decide⟩,
    ⟨prime_26387, by decide, by decide⟩,
    ⟨prime_26393, by decide, by decide⟩,
    ⟨prime_26399, by decide, by decide⟩,
    ⟨prime_26407, by decide, by decide⟩,
    ⟨prime_26417, by decide, by decide⟩,
    ⟨prime_26423, by decide, by decide⟩,
    ⟨prime_26431, by decide, by decide⟩,
    ⟨prime_26437, by decide, by decide⟩,
    ⟨prime_26449, by decide, by decide⟩,
    ⟨prime_26459, by decide, by decide⟩,
    ⟨prime_26479, by decide, by decide⟩,
    ⟨prime_26489, by decide, by decide⟩,
    ⟨prime_26497, by decide, by decide⟩,
    ⟨prime_26501, by decide, by decide⟩,
    ⟨prime_26513, by decide, by decide⟩,
    ⟨prime_26539, by decide, by decide⟩,
    ⟨prime_26557, by decide, by decide⟩,
    ⟨prime_26561, by decide, by decide⟩,
    ⟨prime_26573, by decide, by decide⟩,
    ⟨prime_26591, by decide, by decide⟩,
    ⟨prime_26597, by decide, by decide⟩,
    ⟨prime_26627, by decide, by decide⟩,
    ⟨prime_26633, by decide, by decide⟩,
    ⟨prime_26641, by decide, by decide⟩,
    ⟨prime_26647, by decide, by decide⟩,
    ⟨prime_26669, by decide, by decide⟩,
    ⟨prime_26681, by decide, by decide⟩,
    ⟨prime_26683, by decide, by decide⟩,
    ⟨prime_26687, by decide, by decide⟩,
    ⟨prime_26693, by decide, by decide⟩,
    ⟨prime_26699, by decide, by decide⟩,
    ⟨prime_26701, by decide, by decide⟩,
    ⟨prime_26711, by decide, by decide⟩,
    ⟨prime_26713, by decide, by decide⟩,
    ⟨prime_26717, by decide, by decide⟩,
    ⟨prime_26723, by decide, by decide⟩,
    ⟨prime_26729, by decide, by decide⟩,
    ⟨prime_26731, by decide, by decide⟩,
    ⟨prime_26737, by decide, by decide⟩,
    ⟨prime_26759, by decide, by decide⟩,
    ⟨prime_26777, by decide, by decide⟩,
    ⟨prime_26783, by decide, by decide⟩,
    ⟨prime_26801, by decide, by decide⟩,
    ⟨prime_26813, by decide, by decide⟩,
    ⟨prime_26821, by decide, by decide⟩,
    ⟨prime_26833, by decide, by decide⟩,
    ⟨prime_26839, by decide, by decide⟩,
    ⟨prime_26849, by decide, by decide⟩
  ⟩

end B045
end Sude.Lucas.Generated
