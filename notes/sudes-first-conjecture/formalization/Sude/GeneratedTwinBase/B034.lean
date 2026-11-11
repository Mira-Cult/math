import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0075
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0081
import Sude.GeneratedFTT.N0084
import Sude.GeneratedFTT.N0087
import Sude.GeneratedFTT.N0088
import Sude.GeneratedFTT.N0106
import Sude.GeneratedFTT.N0113
import Sude.GeneratedFTT.N0114
import Sude.GeneratedFTT.N0118
import Sude.GeneratedFTT.N0119
import Sude.GeneratedFTT.N0126
import Sude.GeneratedFTT.N0139
import Sude.GeneratedTwinBase.M001
import Sude.GeneratedTwinBase.B032

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B034
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [19211, 19213, 19219, 19231, 19237, 19249, 19259, 19267, 19273, 19289, 19301, 19309, 19319, 19333, 19373, 19379, 19381, 19387, 19391, 19403, 19417, 19421, 19423, 19427, 19429, 19433, 19441, 19447, 19457, 19463, 19469, 19471, 19477, 19483, 19489, 19501, 19507, 19531, 19541, 19543, 19553, 19559, 19571, 19577, 19583, 19597, 19603, 19609, 19661, 19681, 19687, 19697, 19699, 19709, 19717, 19727, 19739, 19751, 19753, 19759, 19763, 19777, 19793, 19801]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_19211, by decide, by decide⟩,
    ⟨prime_19213, by decide, by decide⟩,
    ⟨prime_19219, by decide, by decide⟩,
    ⟨prime_19231, by decide, by decide⟩,
    ⟨prime_19237, by decide, by decide⟩,
    ⟨prime_19249, by decide, by decide⟩,
    ⟨prime_19259, by decide, by decide⟩,
    ⟨prime_19267, by decide, by decide⟩,
    ⟨prime_19273, by decide, by decide⟩,
    ⟨prime_19289, by decide, by decide⟩,
    ⟨prime_19301, by decide, by decide⟩,
    ⟨prime_19309, by decide, by decide⟩,
    ⟨prime_19319, by decide, by decide⟩,
    ⟨prime_19333, by decide, by decide⟩,
    ⟨prime_19373, by decide, by decide⟩,
    ⟨prime_19379, by decide, by decide⟩,
    ⟨prime_19381, by decide, by decide⟩,
    ⟨prime_19387, by decide, by decide⟩,
    ⟨prime_19391, by decide, by decide⟩,
    ⟨prime_19403, by decide, by decide⟩,
    ⟨prime_19417, by decide, by decide⟩,
    ⟨prime_19421, by decide, by decide⟩,
    ⟨prime_19423, by decide, by decide⟩,
    ⟨prime_19427, by decide, by decide⟩,
    ⟨prime_19429, by decide, by decide⟩,
    ⟨prime_19433, by decide, by decide⟩,
    ⟨prime_19441, by decide, by decide⟩,
    ⟨prime_19447, by decide, by decide⟩,
    ⟨prime_19457, by decide, by decide⟩,
    ⟨prime_19463, by decide, by decide⟩,
    ⟨prime_19469, by decide, by decide⟩,
    ⟨prime_19471, by decide, by decide⟩,
    ⟨prime_19477, by decide, by decide⟩,
    ⟨prime_19483, by decide, by decide⟩,
    ⟨prime_19489, by decide, by decide⟩,
    ⟨prime_19501, by decide, by decide⟩,
    ⟨prime_19507, by decide, by decide⟩,
    ⟨prime_19531, by decide, by decide⟩,
    ⟨prime_19541, by decide, by decide⟩,
    ⟨prime_19543, by decide, by decide⟩,
    ⟨prime_19553, by decide, by decide⟩,
    ⟨prime_19559, by decide, by decide⟩,
    ⟨prime_19571, by decide, by decide⟩,
    ⟨prime_19577, by decide, by decide⟩,
    ⟨prime_19583, by decide, by decide⟩,
    ⟨prime_19597, by decide, by decide⟩,
    ⟨prime_19603, by decide, by decide⟩,
    ⟨prime_19609, by decide, by decide⟩,
    ⟨prime_19661, by decide, by decide⟩,
    ⟨prime_19681, by decide, by decide⟩,
    ⟨prime_19687, by decide, by decide⟩,
    ⟨prime_19697, by decide, by decide⟩,
    ⟨prime_19699, by decide, by decide⟩,
    ⟨prime_19709, by decide, by decide⟩,
    ⟨prime_19717, by decide, by decide⟩,
    ⟨prime_19727, by decide, by decide⟩,
    ⟨prime_19739, by decide, by decide⟩,
    ⟨prime_19751, by decide, by decide⟩,
    ⟨prime_19753, by decide, by decide⟩,
    ⟨prime_19759, by decide, by decide⟩,
    ⟨prime_19763, by decide, by decide⟩,
    ⟨prime_19777, by decide, by decide⟩,
    ⟨prime_19793, by decide, by decide⟩,
    ⟨prime_19801, by decide, by decide⟩
  ⟩

end B034
end Sude.Lucas.Generated
