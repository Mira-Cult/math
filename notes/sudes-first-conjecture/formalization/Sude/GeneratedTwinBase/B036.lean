import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0064
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0083
import Sude.GeneratedFTT.N0085
import Sude.GeneratedFTT.N0086
import Sude.GeneratedFTT.N0094
import Sude.GeneratedFTT.N0104
import Sude.GeneratedFTT.N0110
import Sude.GeneratedFTT.N0111
import Sude.GeneratedFTT.N0120
import Sude.GeneratedFTT.N0122
import Sude.GeneratedFTT.N0123
import Sude.GeneratedFTT.N0130
import Sude.GeneratedFTT.N0141
import Sude.GeneratedFTT.N0146
import Sude.GeneratedTwinBase.M001
import Sude.GeneratedTwinBase.B034

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B036
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [20407, 20411, 20431, 20441, 20443, 20477, 20479, 20483, 20507, 20509, 20521, 20533, 20543, 20549, 20551, 20563, 20593, 20599, 20611, 20627, 20639, 20641, 20663, 20681, 20693, 20707, 20717, 20719, 20731, 20743, 20747, 20749, 20753, 20759, 20771, 20773, 20789, 20807, 20809, 20849, 20857, 20873, 20879, 20887, 20897, 20899, 20903, 20921, 20929, 20939, 20947, 20959, 20963, 20981, 20983, 21001, 21011, 21013, 21017, 21019, 21023, 21031, 21059, 21061]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_20407, by decide, by decide⟩,
    ⟨prime_20411, by decide, by decide⟩,
    ⟨prime_20431, by decide, by decide⟩,
    ⟨prime_20441, by decide, by decide⟩,
    ⟨prime_20443, by decide, by decide⟩,
    ⟨prime_20477, by decide, by decide⟩,
    ⟨prime_20479, by decide, by decide⟩,
    ⟨prime_20483, by decide, by decide⟩,
    ⟨prime_20507, by decide, by decide⟩,
    ⟨prime_20509, by decide, by decide⟩,
    ⟨prime_20521, by decide, by decide⟩,
    ⟨prime_20533, by decide, by decide⟩,
    ⟨prime_20543, by decide, by decide⟩,
    ⟨prime_20549, by decide, by decide⟩,
    ⟨prime_20551, by decide, by decide⟩,
    ⟨prime_20563, by decide, by decide⟩,
    ⟨prime_20593, by decide, by decide⟩,
    ⟨prime_20599, by decide, by decide⟩,
    ⟨prime_20611, by decide, by decide⟩,
    ⟨prime_20627, by decide, by decide⟩,
    ⟨prime_20639, by decide, by decide⟩,
    ⟨prime_20641, by decide, by decide⟩,
    ⟨prime_20663, by decide, by decide⟩,
    ⟨prime_20681, by decide, by decide⟩,
    ⟨prime_20693, by decide, by decide⟩,
    ⟨prime_20707, by decide, by decide⟩,
    ⟨prime_20717, by decide, by decide⟩,
    ⟨prime_20719, by decide, by decide⟩,
    ⟨prime_20731, by decide, by decide⟩,
    ⟨prime_20743, by decide, by decide⟩,
    ⟨prime_20747, by decide, by decide⟩,
    ⟨prime_20749, by decide, by decide⟩,
    ⟨prime_20753, by decide, by decide⟩,
    ⟨prime_20759, by decide, by decide⟩,
    ⟨prime_20771, by decide, by decide⟩,
    ⟨prime_20773, by decide, by decide⟩,
    ⟨prime_20789, by decide, by decide⟩,
    ⟨prime_20807, by decide, by decide⟩,
    ⟨prime_20809, by decide, by decide⟩,
    ⟨prime_20849, by decide, by decide⟩,
    ⟨prime_20857, by decide, by decide⟩,
    ⟨prime_20873, by decide, by decide⟩,
    ⟨prime_20879, by decide, by decide⟩,
    ⟨prime_20887, by decide, by decide⟩,
    ⟨prime_20897, by decide, by decide⟩,
    ⟨prime_20899, by decide, by decide⟩,
    ⟨prime_20903, by decide, by decide⟩,
    ⟨prime_20921, by decide, by decide⟩,
    ⟨prime_20929, by decide, by decide⟩,
    ⟨prime_20939, by decide, by decide⟩,
    ⟨prime_20947, by decide, by decide⟩,
    ⟨prime_20959, by decide, by decide⟩,
    ⟨prime_20963, by decide, by decide⟩,
    ⟨prime_20981, by decide, by decide⟩,
    ⟨prime_20983, by decide, by decide⟩,
    ⟨prime_21001, by decide, by decide⟩,
    ⟨prime_21011, by decide, by decide⟩,
    ⟨prime_21013, by decide, by decide⟩,
    ⟨prime_21017, by decide, by decide⟩,
    ⟨prime_21019, by decide, by decide⟩,
    ⟨prime_21023, by decide, by decide⟩,
    ⟨prime_21031, by decide, by decide⟩,
    ⟨prime_21059, by decide, by decide⟩,
    ⟨prime_21061, by decide, by decide⟩
  ⟩

end B036
end Sude.Lucas.Generated
