import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0079
import Sude.GeneratedFTT.N0087
import Sude.GeneratedFTT.N0093
import Sude.GeneratedTwinBase.M000
import Sude.GeneratedTwinBase.B014

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B016
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [8171, 8179, 8191, 8209, 8219, 8221, 8231, 8233, 8237, 8243, 8263, 8269, 8273, 8287, 8291, 8293, 8297, 8311, 8317, 8329, 8353, 8363, 8369, 8377, 8387, 8389, 8419, 8423, 8429, 8431, 8443, 8447, 8461, 8467, 8501, 8513, 8521, 8527, 8537, 8539, 8543, 8563, 8573, 8581, 8597, 8599, 8609, 8623, 8627, 8629, 8641, 8647, 8663, 8669, 8677, 8681, 8689, 8693, 8699, 8707, 8713, 8719, 8731, 8737]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_8171, by decide, by decide⟩,
    ⟨prime_8179, by decide, by decide⟩,
    ⟨prime_8191, by decide, by decide⟩,
    ⟨prime_8209, by decide, by decide⟩,
    ⟨prime_8219, by decide, by decide⟩,
    ⟨prime_8221, by decide, by decide⟩,
    ⟨prime_8231, by decide, by decide⟩,
    ⟨prime_8233, by decide, by decide⟩,
    ⟨prime_8237, by decide, by decide⟩,
    ⟨prime_8243, by decide, by decide⟩,
    ⟨prime_8263, by decide, by decide⟩,
    ⟨prime_8269, by decide, by decide⟩,
    ⟨prime_8273, by decide, by decide⟩,
    ⟨prime_8287, by decide, by decide⟩,
    ⟨prime_8291, by decide, by decide⟩,
    ⟨prime_8293, by decide, by decide⟩,
    ⟨prime_8297, by decide, by decide⟩,
    ⟨prime_8311, by decide, by decide⟩,
    ⟨prime_8317, by decide, by decide⟩,
    ⟨prime_8329, by decide, by decide⟩,
    ⟨prime_8353, by decide, by decide⟩,
    ⟨prime_8363, by decide, by decide⟩,
    ⟨prime_8369, by decide, by decide⟩,
    ⟨prime_8377, by decide, by decide⟩,
    ⟨prime_8387, by decide, by decide⟩,
    ⟨prime_8389, by decide, by decide⟩,
    ⟨prime_8419, by decide, by decide⟩,
    ⟨prime_8423, by decide, by decide⟩,
    ⟨prime_8429, by decide, by decide⟩,
    ⟨prime_8431, by decide, by decide⟩,
    ⟨prime_8443, by decide, by decide⟩,
    ⟨prime_8447, by decide, by decide⟩,
    ⟨prime_8461, by decide, by decide⟩,
    ⟨prime_8467, by decide, by decide⟩,
    ⟨prime_8501, by decide, by decide⟩,
    ⟨prime_8513, by decide, by decide⟩,
    ⟨prime_8521, by decide, by decide⟩,
    ⟨prime_8527, by decide, by decide⟩,
    ⟨prime_8537, by decide, by decide⟩,
    ⟨prime_8539, by decide, by decide⟩,
    ⟨prime_8543, by decide, by decide⟩,
    ⟨prime_8563, by decide, by decide⟩,
    ⟨prime_8573, by decide, by decide⟩,
    ⟨prime_8581, by decide, by decide⟩,
    ⟨prime_8597, by decide, by decide⟩,
    ⟨prime_8599, by decide, by decide⟩,
    ⟨prime_8609, by decide, by decide⟩,
    ⟨prime_8623, by decide, by decide⟩,
    ⟨prime_8627, by decide, by decide⟩,
    ⟨prime_8629, by decide, by decide⟩,
    ⟨prime_8641, by decide, by decide⟩,
    ⟨prime_8647, by decide, by decide⟩,
    ⟨prime_8663, by decide, by decide⟩,
    ⟨prime_8669, by decide, by decide⟩,
    ⟨prime_8677, by decide, by decide⟩,
    ⟨prime_8681, by decide, by decide⟩,
    ⟨prime_8689, by decide, by decide⟩,
    ⟨prime_8693, by decide, by decide⟩,
    ⟨prime_8699, by decide, by decide⟩,
    ⟨prime_8707, by decide, by decide⟩,
    ⟨prime_8713, by decide, by decide⟩,
    ⟨prime_8719, by decide, by decide⟩,
    ⟨prime_8731, by decide, by decide⟩,
    ⟨prime_8737, by decide, by decide⟩
  ⟩

end B016
end Sude.Lucas.Generated
