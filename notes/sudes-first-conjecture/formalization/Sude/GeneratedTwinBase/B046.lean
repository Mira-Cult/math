import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0074
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0079
import Sude.GeneratedFTT.N0084
import Sude.GeneratedFTT.N0088
import Sude.GeneratedFTT.N0095
import Sude.GeneratedFTT.N0103
import Sude.GeneratedFTT.N0104
import Sude.GeneratedFTT.N0115
import Sude.GeneratedFTT.N0121
import Sude.GeneratedFTT.N0123
import Sude.GeneratedFTT.N0124
import Sude.GeneratedFTT.N0126
import Sude.GeneratedFTT.N0127
import Sude.GeneratedFTT.N0138
import Sude.GeneratedFTT.N0141
import Sude.GeneratedFTT.N0149
import Sude.GeneratedFTT.N0150
import Sude.GeneratedTwinBase.M002
import Sude.GeneratedTwinBase.B044

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B046
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [26861, 26863, 26879, 26881, 26891, 26893, 26903, 26921, 26927, 26947, 26951, 26953, 26959, 26981, 26987, 26993, 27011, 27017, 27031, 27043, 27059, 27061, 27067, 27073, 27077, 27091, 27103, 27107, 27109, 27127, 27143, 27179, 27191, 27197, 27211, 27239, 27241, 27253, 27259, 27271, 27277, 27281, 27283, 27299, 27329, 27337, 27361, 27367, 27397, 27407, 27409, 27427, 27431, 27437, 27449, 27457, 27479, 27481, 27487, 27509, 27527, 27529, 27539, 27541]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_26861, by decide, by decide⟩,
    ⟨prime_26863, by decide, by decide⟩,
    ⟨prime_26879, by decide, by decide⟩,
    ⟨prime_26881, by decide, by decide⟩,
    ⟨prime_26891, by decide, by decide⟩,
    ⟨prime_26893, by decide, by decide⟩,
    ⟨prime_26903, by decide, by decide⟩,
    ⟨prime_26921, by decide, by decide⟩,
    ⟨prime_26927, by decide, by decide⟩,
    ⟨prime_26947, by decide, by decide⟩,
    ⟨prime_26951, by decide, by decide⟩,
    ⟨prime_26953, by decide, by decide⟩,
    ⟨prime_26959, by decide, by decide⟩,
    ⟨prime_26981, by decide, by decide⟩,
    ⟨prime_26987, by decide, by decide⟩,
    ⟨prime_26993, by decide, by decide⟩,
    ⟨prime_27011, by decide, by decide⟩,
    ⟨prime_27017, by decide, by decide⟩,
    ⟨prime_27031, by decide, by decide⟩,
    ⟨prime_27043, by decide, by decide⟩,
    ⟨prime_27059, by decide, by decide⟩,
    ⟨prime_27061, by decide, by decide⟩,
    ⟨prime_27067, by decide, by decide⟩,
    ⟨prime_27073, by decide, by decide⟩,
    ⟨prime_27077, by decide, by decide⟩,
    ⟨prime_27091, by decide, by decide⟩,
    ⟨prime_27103, by decide, by decide⟩,
    ⟨prime_27107, by decide, by decide⟩,
    ⟨prime_27109, by decide, by decide⟩,
    ⟨prime_27127, by decide, by decide⟩,
    ⟨prime_27143, by decide, by decide⟩,
    ⟨prime_27179, by decide, by decide⟩,
    ⟨prime_27191, by decide, by decide⟩,
    ⟨prime_27197, by decide, by decide⟩,
    ⟨prime_27211, by decide, by decide⟩,
    ⟨prime_27239, by decide, by decide⟩,
    ⟨prime_27241, by decide, by decide⟩,
    ⟨prime_27253, by decide, by decide⟩,
    ⟨prime_27259, by decide, by decide⟩,
    ⟨prime_27271, by decide, by decide⟩,
    ⟨prime_27277, by decide, by decide⟩,
    ⟨prime_27281, by decide, by decide⟩,
    ⟨prime_27283, by decide, by decide⟩,
    ⟨prime_27299, by decide, by decide⟩,
    ⟨prime_27329, by decide, by decide⟩,
    ⟨prime_27337, by decide, by decide⟩,
    ⟨prime_27361, by decide, by decide⟩,
    ⟨prime_27367, by decide, by decide⟩,
    ⟨prime_27397, by decide, by decide⟩,
    ⟨prime_27407, by decide, by decide⟩,
    ⟨prime_27409, by decide, by decide⟩,
    ⟨prime_27427, by decide, by decide⟩,
    ⟨prime_27431, by decide, by decide⟩,
    ⟨prime_27437, by decide, by decide⟩,
    ⟨prime_27449, by decide, by decide⟩,
    ⟨prime_27457, by decide, by decide⟩,
    ⟨prime_27479, by decide, by decide⟩,
    ⟨prime_27481, by decide, by decide⟩,
    ⟨prime_27487, by decide, by decide⟩,
    ⟨prime_27509, by decide, by decide⟩,
    ⟨prime_27527, by decide, by decide⟩,
    ⟨prime_27529, by decide, by decide⟩,
    ⟨prime_27539, by decide, by decide⟩,
    ⟨prime_27541, by decide, by decide⟩
  ⟩

end B046
end Sude.Lucas.Generated
