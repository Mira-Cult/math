import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0053
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0075
import Sude.GeneratedFTT.N0079
import Sude.GeneratedFTT.N0082
import Sude.GeneratedFTT.N0091
import Sude.GeneratedFTT.N0104
import Sude.GeneratedFTT.N0105
import Sude.GeneratedFTT.N0108
import Sude.GeneratedFTT.N0110
import Sude.GeneratedFTT.N0111
import Sude.GeneratedFTT.N0114
import Sude.GeneratedFTT.N0126
import Sude.GeneratedFTT.N0129
import Sude.GeneratedFTT.N0136
import Sude.GeneratedFTT.N0144
import Sude.GeneratedFTT.N0147
import Sude.GeneratedTwinBase.M002
import Sude.GeneratedTwinBase.B041

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B043
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [24919, 24923, 24943, 24953, 24967, 24971, 24977, 24979, 24989, 25013, 25031, 25033, 25037, 25057, 25073, 25087, 25097, 25111, 25117, 25121, 25127, 25147, 25153, 25163, 25169, 25171, 25183, 25189, 25219, 25229, 25237, 25243, 25247, 25253, 25261, 25301, 25303, 25307, 25309, 25321, 25339, 25343, 25349, 25357, 25367, 25373, 25391, 25409, 25411, 25423, 25439, 25447, 25453, 25457, 25463, 25469, 25471, 25523, 25537, 25541, 25561, 25577, 25579, 25583]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_24919, by decide, by decide⟩,
    ⟨prime_24923, by decide, by decide⟩,
    ⟨prime_24943, by decide, by decide⟩,
    ⟨prime_24953, by decide, by decide⟩,
    ⟨prime_24967, by decide, by decide⟩,
    ⟨prime_24971, by decide, by decide⟩,
    ⟨prime_24977, by decide, by decide⟩,
    ⟨prime_24979, by decide, by decide⟩,
    ⟨prime_24989, by decide, by decide⟩,
    ⟨prime_25013, by decide, by decide⟩,
    ⟨prime_25031, by decide, by decide⟩,
    ⟨prime_25033, by decide, by decide⟩,
    ⟨prime_25037, by decide, by decide⟩,
    ⟨prime_25057, by decide, by decide⟩,
    ⟨prime_25073, by decide, by decide⟩,
    ⟨prime_25087, by decide, by decide⟩,
    ⟨prime_25097, by decide, by decide⟩,
    ⟨prime_25111, by decide, by decide⟩,
    ⟨prime_25117, by decide, by decide⟩,
    ⟨prime_25121, by decide, by decide⟩,
    ⟨prime_25127, by decide, by decide⟩,
    ⟨prime_25147, by decide, by decide⟩,
    ⟨prime_25153, by decide, by decide⟩,
    ⟨prime_25163, by decide, by decide⟩,
    ⟨prime_25169, by decide, by decide⟩,
    ⟨prime_25171, by decide, by decide⟩,
    ⟨prime_25183, by decide, by decide⟩,
    ⟨prime_25189, by decide, by decide⟩,
    ⟨prime_25219, by decide, by decide⟩,
    ⟨prime_25229, by decide, by decide⟩,
    ⟨prime_25237, by decide, by decide⟩,
    ⟨prime_25243, by decide, by decide⟩,
    ⟨prime_25247, by decide, by decide⟩,
    ⟨prime_25253, by decide, by decide⟩,
    ⟨prime_25261, by decide, by decide⟩,
    ⟨prime_25301, by decide, by decide⟩,
    ⟨prime_25303, by decide, by decide⟩,
    ⟨prime_25307, by decide, by decide⟩,
    ⟨prime_25309, by decide, by decide⟩,
    ⟨prime_25321, by decide, by decide⟩,
    ⟨prime_25339, by decide, by decide⟩,
    ⟨prime_25343, by decide, by decide⟩,
    ⟨prime_25349, by decide, by decide⟩,
    ⟨prime_25357, by decide, by decide⟩,
    ⟨prime_25367, by decide, by decide⟩,
    ⟨prime_25373, by decide, by decide⟩,
    ⟨prime_25391, by decide, by decide⟩,
    ⟨prime_25409, by decide, by decide⟩,
    ⟨prime_25411, by decide, by decide⟩,
    ⟨prime_25423, by decide, by decide⟩,
    ⟨prime_25439, by decide, by decide⟩,
    ⟨prime_25447, by decide, by decide⟩,
    ⟨prime_25453, by decide, by decide⟩,
    ⟨prime_25457, by decide, by decide⟩,
    ⟨prime_25463, by decide, by decide⟩,
    ⟨prime_25469, by decide, by decide⟩,
    ⟨prime_25471, by decide, by decide⟩,
    ⟨prime_25523, by decide, by decide⟩,
    ⟨prime_25537, by decide, by decide⟩,
    ⟨prime_25541, by decide, by decide⟩,
    ⟨prime_25561, by decide, by decide⟩,
    ⟨prime_25577, by decide, by decide⟩,
    ⟨prime_25579, by decide, by decide⟩,
    ⟨prime_25583, by decide, by decide⟩
  ⟩

end B043
end Sude.Lucas.Generated
