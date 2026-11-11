import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0074
import Sude.GeneratedFTT.N0083
import Sude.GeneratedFTT.N0084
import Sude.GeneratedFTT.N0092
import Sude.GeneratedFTT.N0096
import Sude.GeneratedFTT.N0097
import Sude.GeneratedFTT.N0104
import Sude.GeneratedFTT.N0105
import Sude.GeneratedFTT.N0113
import Sude.GeneratedFTT.N0116
import Sude.GeneratedFTT.N0121
import Sude.GeneratedFTT.N0122
import Sude.GeneratedFTT.N0127
import Sude.GeneratedFTT.N0137
import Sude.GeneratedFTT.N0139
import Sude.GeneratedFTT.N0150
import Sude.GeneratedTwinBase.M000
import Sude.GeneratedTwinBase.B029

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B031
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [17257, 17291, 17293, 17299, 17317, 17321, 17327, 17333, 17341, 17351, 17359, 17377, 17383, 17387, 17389, 17393, 17401, 17417, 17419, 17431, 17443, 17449, 17467, 17471, 17477, 17483, 17489, 17491, 17497, 17509, 17519, 17539, 17551, 17569, 17573, 17579, 17581, 17597, 17599, 17609, 17623, 17627, 17657, 17659, 17669, 17681, 17683, 17707, 17713, 17729, 17737, 17747, 17749, 17761, 17783, 17789, 17791, 17807, 17827, 17837, 17839, 17851, 17863, 17881]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_17257, by decide, by decide⟩,
    ⟨prime_17291, by decide, by decide⟩,
    ⟨prime_17293, by decide, by decide⟩,
    ⟨prime_17299, by decide, by decide⟩,
    ⟨prime_17317, by decide, by decide⟩,
    ⟨prime_17321, by decide, by decide⟩,
    ⟨prime_17327, by decide, by decide⟩,
    ⟨prime_17333, by decide, by decide⟩,
    ⟨prime_17341, by decide, by decide⟩,
    ⟨prime_17351, by decide, by decide⟩,
    ⟨prime_17359, by decide, by decide⟩,
    ⟨prime_17377, by decide, by decide⟩,
    ⟨prime_17383, by decide, by decide⟩,
    ⟨prime_17387, by decide, by decide⟩,
    ⟨prime_17389, by decide, by decide⟩,
    ⟨prime_17393, by decide, by decide⟩,
    ⟨prime_17401, by decide, by decide⟩,
    ⟨prime_17417, by decide, by decide⟩,
    ⟨prime_17419, by decide, by decide⟩,
    ⟨prime_17431, by decide, by decide⟩,
    ⟨prime_17443, by decide, by decide⟩,
    ⟨prime_17449, by decide, by decide⟩,
    ⟨prime_17467, by decide, by decide⟩,
    ⟨prime_17471, by decide, by decide⟩,
    ⟨prime_17477, by decide, by decide⟩,
    ⟨prime_17483, by decide, by decide⟩,
    ⟨prime_17489, by decide, by decide⟩,
    ⟨prime_17491, by decide, by decide⟩,
    ⟨prime_17497, by decide, by decide⟩,
    ⟨prime_17509, by decide, by decide⟩,
    ⟨prime_17519, by decide, by decide⟩,
    ⟨prime_17539, by decide, by decide⟩,
    ⟨prime_17551, by decide, by decide⟩,
    ⟨prime_17569, by decide, by decide⟩,
    ⟨prime_17573, by decide, by decide⟩,
    ⟨prime_17579, by decide, by decide⟩,
    ⟨prime_17581, by decide, by decide⟩,
    ⟨prime_17597, by decide, by decide⟩,
    ⟨prime_17599, by decide, by decide⟩,
    ⟨prime_17609, by decide, by decide⟩,
    ⟨prime_17623, by decide, by decide⟩,
    ⟨prime_17627, by decide, by decide⟩,
    ⟨prime_17657, by decide, by decide⟩,
    ⟨prime_17659, by decide, by decide⟩,
    ⟨prime_17669, by decide, by decide⟩,
    ⟨prime_17681, by decide, by decide⟩,
    ⟨prime_17683, by decide, by decide⟩,
    ⟨prime_17707, by decide, by decide⟩,
    ⟨prime_17713, by decide, by decide⟩,
    ⟨prime_17729, by decide, by decide⟩,
    ⟨prime_17737, by decide, by decide⟩,
    ⟨prime_17747, by decide, by decide⟩,
    ⟨prime_17749, by decide, by decide⟩,
    ⟨prime_17761, by decide, by decide⟩,
    ⟨prime_17783, by decide, by decide⟩,
    ⟨prime_17789, by decide, by decide⟩,
    ⟨prime_17791, by decide, by decide⟩,
    ⟨prime_17807, by decide, by decide⟩,
    ⟨prime_17827, by decide, by decide⟩,
    ⟨prime_17837, by decide, by decide⟩,
    ⟨prime_17839, by decide, by decide⟩,
    ⟨prime_17851, by decide, by decide⟩,
    ⟨prime_17863, by decide, by decide⟩,
    ⟨prime_17881, by decide, by decide⟩
  ⟩

end B031
end Sude.Lucas.Generated
