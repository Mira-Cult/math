import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0064
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0083
import Sude.GeneratedFTT.N0085
import Sude.GeneratedFTT.N0086
import Sude.GeneratedFTT.N0088
import Sude.GeneratedFTT.N0097
import Sude.GeneratedFTT.N0113
import Sude.GeneratedFTT.N0117
import Sude.GeneratedFTT.N0121
import Sude.GeneratedFTT.N0147
import Sude.GeneratedTwinBase.M004
import Sude.GeneratedTwinBase.B052

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B054
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [32237, 32251, 32257, 32261, 32297, 32299, 32303, 32309, 32321, 32323, 32327, 32341, 32353, 32359, 32363, 32369, 32371, 32377, 32381, 32401, 32411, 32413, 32423, 32429, 32441, 32443, 32467, 32479, 32491, 32497, 32503, 32507, 32531, 32533, 32537, 32561, 32563, 32569, 32573, 32579, 32587, 32603, 32609, 32611, 32621, 32633, 32647, 32653, 32687, 32693, 32707, 32713, 32717, 32719, 32749]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_32237, by decide, by decide⟩,
    ⟨prime_32251, by decide, by decide⟩,
    ⟨prime_32257, by decide, by decide⟩,
    ⟨prime_32261, by decide, by decide⟩,
    ⟨prime_32297, by decide, by decide⟩,
    ⟨prime_32299, by decide, by decide⟩,
    ⟨prime_32303, by decide, by decide⟩,
    ⟨prime_32309, by decide, by decide⟩,
    ⟨prime_32321, by decide, by decide⟩,
    ⟨prime_32323, by decide, by decide⟩,
    ⟨prime_32327, by decide, by decide⟩,
    ⟨prime_32341, by decide, by decide⟩,
    ⟨prime_32353, by decide, by decide⟩,
    ⟨prime_32359, by decide, by decide⟩,
    ⟨prime_32363, by decide, by decide⟩,
    ⟨prime_32369, by decide, by decide⟩,
    ⟨prime_32371, by decide, by decide⟩,
    ⟨prime_32377, by decide, by decide⟩,
    ⟨prime_32381, by decide, by decide⟩,
    ⟨prime_32401, by decide, by decide⟩,
    ⟨prime_32411, by decide, by decide⟩,
    ⟨prime_32413, by decide, by decide⟩,
    ⟨prime_32423, by decide, by decide⟩,
    ⟨prime_32429, by decide, by decide⟩,
    ⟨prime_32441, by decide, by decide⟩,
    ⟨prime_32443, by decide, by decide⟩,
    ⟨prime_32467, by decide, by decide⟩,
    ⟨prime_32479, by decide, by decide⟩,
    ⟨prime_32491, by decide, by decide⟩,
    ⟨prime_32497, by decide, by decide⟩,
    ⟨prime_32503, by decide, by decide⟩,
    ⟨prime_32507, by decide, by decide⟩,
    ⟨prime_32531, by decide, by decide⟩,
    ⟨prime_32533, by decide, by decide⟩,
    ⟨prime_32537, by decide, by decide⟩,
    ⟨prime_32561, by decide, by decide⟩,
    ⟨prime_32563, by decide, by decide⟩,
    ⟨prime_32569, by decide, by decide⟩,
    ⟨prime_32573, by decide, by decide⟩,
    ⟨prime_32579, by decide, by decide⟩,
    ⟨prime_32587, by decide, by decide⟩,
    ⟨prime_32603, by decide, by decide⟩,
    ⟨prime_32609, by decide, by decide⟩,
    ⟨prime_32611, by decide, by decide⟩,
    ⟨prime_32621, by decide, by decide⟩,
    ⟨prime_32633, by decide, by decide⟩,
    ⟨prime_32647, by decide, by decide⟩,
    ⟨prime_32653, by decide, by decide⟩,
    ⟨prime_32687, by decide, by decide⟩,
    ⟨prime_32693, by decide, by decide⟩,
    ⟨prime_32707, by decide, by decide⟩,
    ⟨prime_32713, by decide, by decide⟩,
    ⟨prime_32717, by decide, by decide⟩,
    ⟨prime_32719, by decide, by decide⟩,
    ⟨prime_32749, by decide, by decide⟩
  ⟩

end B054
end Sude.Lucas.Generated
