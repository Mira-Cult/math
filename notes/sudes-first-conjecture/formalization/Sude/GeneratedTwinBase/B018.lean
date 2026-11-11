import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0087
import Sude.GeneratedFTT.N0088
import Sude.GeneratedFTT.N0092
import Sude.GeneratedFTT.N0104
import Sude.GeneratedFTT.N0107
import Sude.GeneratedFTT.N0110
import Sude.GeneratedFTT.N0111
import Sude.GeneratedTwinBase.M000
import Sude.GeneratedTwinBase.B016

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B018
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [9323, 9337, 9341, 9343, 9349, 9371, 9377, 9391, 9397, 9403, 9413, 9419, 9421, 9431, 9433, 9437, 9439, 9461, 9463, 9467, 9473, 9479, 9491, 9497, 9511, 9521, 9533, 9539, 9547, 9551, 9587, 9601, 9613, 9619, 9623, 9629, 9631, 9643, 9649, 9661, 9677, 9679, 9689, 9697, 9719, 9721, 9733, 9739, 9743, 9749, 9767, 9769, 9781, 9787, 9791, 9803, 9811, 9817, 9829, 9833, 9839, 9851, 9857, 9859]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_9323, by decide, by decide⟩,
    ⟨prime_9337, by decide, by decide⟩,
    ⟨prime_9341, by decide, by decide⟩,
    ⟨prime_9343, by decide, by decide⟩,
    ⟨prime_9349, by decide, by decide⟩,
    ⟨prime_9371, by decide, by decide⟩,
    ⟨prime_9377, by decide, by decide⟩,
    ⟨prime_9391, by decide, by decide⟩,
    ⟨prime_9397, by decide, by decide⟩,
    ⟨prime_9403, by decide, by decide⟩,
    ⟨prime_9413, by decide, by decide⟩,
    ⟨prime_9419, by decide, by decide⟩,
    ⟨prime_9421, by decide, by decide⟩,
    ⟨prime_9431, by decide, by decide⟩,
    ⟨prime_9433, by decide, by decide⟩,
    ⟨prime_9437, by decide, by decide⟩,
    ⟨prime_9439, by decide, by decide⟩,
    ⟨prime_9461, by decide, by decide⟩,
    ⟨prime_9463, by decide, by decide⟩,
    ⟨prime_9467, by decide, by decide⟩,
    ⟨prime_9473, by decide, by decide⟩,
    ⟨prime_9479, by decide, by decide⟩,
    ⟨prime_9491, by decide, by decide⟩,
    ⟨prime_9497, by decide, by decide⟩,
    ⟨prime_9511, by decide, by decide⟩,
    ⟨prime_9521, by decide, by decide⟩,
    ⟨prime_9533, by decide, by decide⟩,
    ⟨prime_9539, by decide, by decide⟩,
    ⟨prime_9547, by decide, by decide⟩,
    ⟨prime_9551, by decide, by decide⟩,
    ⟨prime_9587, by decide, by decide⟩,
    ⟨prime_9601, by decide, by decide⟩,
    ⟨prime_9613, by decide, by decide⟩,
    ⟨prime_9619, by decide, by decide⟩,
    ⟨prime_9623, by decide, by decide⟩,
    ⟨prime_9629, by decide, by decide⟩,
    ⟨prime_9631, by decide, by decide⟩,
    ⟨prime_9643, by decide, by decide⟩,
    ⟨prime_9649, by decide, by decide⟩,
    ⟨prime_9661, by decide, by decide⟩,
    ⟨prime_9677, by decide, by decide⟩,
    ⟨prime_9679, by decide, by decide⟩,
    ⟨prime_9689, by decide, by decide⟩,
    ⟨prime_9697, by decide, by decide⟩,
    ⟨prime_9719, by decide, by decide⟩,
    ⟨prime_9721, by decide, by decide⟩,
    ⟨prime_9733, by decide, by decide⟩,
    ⟨prime_9739, by decide, by decide⟩,
    ⟨prime_9743, by decide, by decide⟩,
    ⟨prime_9749, by decide, by decide⟩,
    ⟨prime_9767, by decide, by decide⟩,
    ⟨prime_9769, by decide, by decide⟩,
    ⟨prime_9781, by decide, by decide⟩,
    ⟨prime_9787, by decide, by decide⟩,
    ⟨prime_9791, by decide, by decide⟩,
    ⟨prime_9803, by decide, by decide⟩,
    ⟨prime_9811, by decide, by decide⟩,
    ⟨prime_9817, by decide, by decide⟩,
    ⟨prime_9829, by decide, by decide⟩,
    ⟨prime_9833, by decide, by decide⟩,
    ⟨prime_9839, by decide, by decide⟩,
    ⟨prime_9851, by decide, by decide⟩,
    ⟨prime_9857, by decide, by decide⟩,
    ⟨prime_9859, by decide, by decide⟩
  ⟩

end B018
end Sude.Lucas.Generated
