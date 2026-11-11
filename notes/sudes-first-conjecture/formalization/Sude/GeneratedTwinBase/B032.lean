import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0078
import Sude.GeneratedFTT.N0079
import Sude.GeneratedFTT.N0080
import Sude.GeneratedFTT.N0081
import Sude.GeneratedFTT.N0082
import Sude.GeneratedFTT.N0086
import Sude.GeneratedFTT.N0093
import Sude.GeneratedFTT.N0102
import Sude.GeneratedFTT.N0106
import Sude.GeneratedFTT.N0125
import Sude.GeneratedFTT.N0132
import Sude.GeneratedFTT.N0139
import Sude.GeneratedFTT.N0140
import Sude.GeneratedTwinBase.M000
import Sude.GeneratedTwinBase.B030

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B032
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [17891, 17903, 17909, 17911, 17921, 17923, 17929, 17939, 17957, 17959, 17971, 17977, 17981, 17987, 17989, 18013, 18041, 18043, 18047, 18049, 18059, 18061, 18077, 18089, 18097, 18119, 18121, 18127, 18131, 18133, 18143, 18149, 18169, 18181, 18191, 18199, 18211, 18217, 18223, 18229, 18233, 18251, 18253, 18257, 18269, 18287, 18289, 18301, 18307, 18311, 18313, 18329, 18341, 18353, 18367, 18371, 18379, 18397, 18401, 18413, 18427, 18433, 18439, 18443]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_17891, by decide, by decide⟩,
    ⟨prime_17903, by decide, by decide⟩,
    ⟨prime_17909, by decide, by decide⟩,
    ⟨prime_17911, by decide, by decide⟩,
    ⟨prime_17921, by decide, by decide⟩,
    ⟨prime_17923, by decide, by decide⟩,
    ⟨prime_17929, by decide, by decide⟩,
    ⟨prime_17939, by decide, by decide⟩,
    ⟨prime_17957, by decide, by decide⟩,
    ⟨prime_17959, by decide, by decide⟩,
    ⟨prime_17971, by decide, by decide⟩,
    ⟨prime_17977, by decide, by decide⟩,
    ⟨prime_17981, by decide, by decide⟩,
    ⟨prime_17987, by decide, by decide⟩,
    ⟨prime_17989, by decide, by decide⟩,
    ⟨prime_18013, by decide, by decide⟩,
    ⟨prime_18041, by decide, by decide⟩,
    ⟨prime_18043, by decide, by decide⟩,
    ⟨prime_18047, by decide, by decide⟩,
    ⟨prime_18049, by decide, by decide⟩,
    ⟨prime_18059, by decide, by decide⟩,
    ⟨prime_18061, by decide, by decide⟩,
    ⟨prime_18077, by decide, by decide⟩,
    ⟨prime_18089, by decide, by decide⟩,
    ⟨prime_18097, by decide, by decide⟩,
    ⟨prime_18119, by decide, by decide⟩,
    ⟨prime_18121, by decide, by decide⟩,
    ⟨prime_18127, by decide, by decide⟩,
    ⟨prime_18131, by decide, by decide⟩,
    ⟨prime_18133, by decide, by decide⟩,
    ⟨prime_18143, by decide, by decide⟩,
    ⟨prime_18149, by decide, by decide⟩,
    ⟨prime_18169, by decide, by decide⟩,
    ⟨prime_18181, by decide, by decide⟩,
    ⟨prime_18191, by decide, by decide⟩,
    ⟨prime_18199, by decide, by decide⟩,
    ⟨prime_18211, by decide, by decide⟩,
    ⟨prime_18217, by decide, by decide⟩,
    ⟨prime_18223, by decide, by decide⟩,
    ⟨prime_18229, by decide, by decide⟩,
    ⟨prime_18233, by decide, by decide⟩,
    ⟨prime_18251, by decide, by decide⟩,
    ⟨prime_18253, by decide, by decide⟩,
    ⟨prime_18257, by decide, by decide⟩,
    ⟨prime_18269, by decide, by decide⟩,
    ⟨prime_18287, by decide, by decide⟩,
    ⟨prime_18289, by decide, by decide⟩,
    ⟨prime_18301, by decide, by decide⟩,
    ⟨prime_18307, by decide, by decide⟩,
    ⟨prime_18311, by decide, by decide⟩,
    ⟨prime_18313, by decide, by decide⟩,
    ⟨prime_18329, by decide, by decide⟩,
    ⟨prime_18341, by decide, by decide⟩,
    ⟨prime_18353, by decide, by decide⟩,
    ⟨prime_18367, by decide, by decide⟩,
    ⟨prime_18371, by decide, by decide⟩,
    ⟨prime_18379, by decide, by decide⟩,
    ⟨prime_18397, by decide, by decide⟩,
    ⟨prime_18401, by decide, by decide⟩,
    ⟨prime_18413, by decide, by decide⟩,
    ⟨prime_18427, by decide, by decide⟩,
    ⟨prime_18433, by decide, by decide⟩,
    ⟨prime_18439, by decide, by decide⟩,
    ⟨prime_18443, by decide, by decide⟩
  ⟩

end B032
end Sude.Lucas.Generated
