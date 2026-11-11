import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0075
import Sude.GeneratedFTT.N0084
import Sude.GeneratedFTT.N0085
import Sude.GeneratedFTT.N0087
import Sude.GeneratedFTT.N0089
import Sude.GeneratedFTT.N0100
import Sude.GeneratedFTT.N0104
import Sude.GeneratedFTT.N0108
import Sude.GeneratedFTT.N0110
import Sude.GeneratedFTT.N0112
import Sude.GeneratedFTT.N0125
import Sude.GeneratedFTT.N0132
import Sude.GeneratedTwinBase.M002
import Sude.GeneratedTwinBase.B042

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B044
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [25589, 25601, 25603, 25609, 25621, 25633, 25639, 25643, 25657, 25667, 25673, 25679, 25693, 25703, 25717, 25733, 25741, 25747, 25759, 25763, 25771, 25793, 25799, 25801, 25819, 25841, 25847, 25849, 25867, 25873, 25889, 25903, 25913, 25919, 25931, 25933, 25939, 25943, 25951, 25969, 25981, 25997, 25999, 26003, 26017, 26021, 26029, 26041, 26053, 26083, 26099, 26107, 26111, 26113, 26119, 26141, 26153, 26161, 26171, 26177, 26183, 26189, 26203, 26209]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_25589, by decide, by decide⟩,
    ⟨prime_25601, by decide, by decide⟩,
    ⟨prime_25603, by decide, by decide⟩,
    ⟨prime_25609, by decide, by decide⟩,
    ⟨prime_25621, by decide, by decide⟩,
    ⟨prime_25633, by decide, by decide⟩,
    ⟨prime_25639, by decide, by decide⟩,
    ⟨prime_25643, by decide, by decide⟩,
    ⟨prime_25657, by decide, by decide⟩,
    ⟨prime_25667, by decide, by decide⟩,
    ⟨prime_25673, by decide, by decide⟩,
    ⟨prime_25679, by decide, by decide⟩,
    ⟨prime_25693, by decide, by decide⟩,
    ⟨prime_25703, by decide, by decide⟩,
    ⟨prime_25717, by decide, by decide⟩,
    ⟨prime_25733, by decide, by decide⟩,
    ⟨prime_25741, by decide, by decide⟩,
    ⟨prime_25747, by decide, by decide⟩,
    ⟨prime_25759, by decide, by decide⟩,
    ⟨prime_25763, by decide, by decide⟩,
    ⟨prime_25771, by decide, by decide⟩,
    ⟨prime_25793, by decide, by decide⟩,
    ⟨prime_25799, by decide, by decide⟩,
    ⟨prime_25801, by decide, by decide⟩,
    ⟨prime_25819, by decide, by decide⟩,
    ⟨prime_25841, by decide, by decide⟩,
    ⟨prime_25847, by decide, by decide⟩,
    ⟨prime_25849, by decide, by decide⟩,
    ⟨prime_25867, by decide, by decide⟩,
    ⟨prime_25873, by decide, by decide⟩,
    ⟨prime_25889, by decide, by decide⟩,
    ⟨prime_25903, by decide, by decide⟩,
    ⟨prime_25913, by decide, by decide⟩,
    ⟨prime_25919, by decide, by decide⟩,
    ⟨prime_25931, by decide, by decide⟩,
    ⟨prime_25933, by decide, by decide⟩,
    ⟨prime_25939, by decide, by decide⟩,
    ⟨prime_25943, by decide, by decide⟩,
    ⟨prime_25951, by decide, by decide⟩,
    ⟨prime_25969, by decide, by decide⟩,
    ⟨prime_25981, by decide, by decide⟩,
    ⟨prime_25997, by decide, by decide⟩,
    ⟨prime_25999, by decide, by decide⟩,
    ⟨prime_26003, by decide, by decide⟩,
    ⟨prime_26017, by decide, by decide⟩,
    ⟨prime_26021, by decide, by decide⟩,
    ⟨prime_26029, by decide, by decide⟩,
    ⟨prime_26041, by decide, by decide⟩,
    ⟨prime_26053, by decide, by decide⟩,
    ⟨prime_26083, by decide, by decide⟩,
    ⟨prime_26099, by decide, by decide⟩,
    ⟨prime_26107, by decide, by decide⟩,
    ⟨prime_26111, by decide, by decide⟩,
    ⟨prime_26113, by decide, by decide⟩,
    ⟨prime_26119, by decide, by decide⟩,
    ⟨prime_26141, by decide, by decide⟩,
    ⟨prime_26153, by decide, by decide⟩,
    ⟨prime_26161, by decide, by decide⟩,
    ⟨prime_26171, by decide, by decide⟩,
    ⟨prime_26177, by decide, by decide⟩,
    ⟨prime_26183, by decide, by decide⟩,
    ⟨prime_26189, by decide, by decide⟩,
    ⟨prime_26203, by decide, by decide⟩,
    ⟨prime_26209, by decide, by decide⟩
  ⟩

end B044
end Sude.Lucas.Generated
