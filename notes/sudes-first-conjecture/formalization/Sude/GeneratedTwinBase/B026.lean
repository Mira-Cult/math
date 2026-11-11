import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0078
import Sude.GeneratedFTT.N0079
import Sude.GeneratedFTT.N0095
import Sude.GeneratedFTT.N0100
import Sude.GeneratedFTT.N0101
import Sude.GeneratedFTT.N0105
import Sude.GeneratedFTT.N0110
import Sude.GeneratedFTT.N0119
import Sude.GeneratedFTT.N0127
import Sude.GeneratedFTT.N0136
import Sude.GeneratedFTT.N0150
import Sude.GeneratedTwinBase.M000
import Sude.GeneratedTwinBase.B024

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B026
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [14153, 14159, 14173, 14177, 14197, 14207, 14221, 14243, 14249, 14251, 14281, 14293, 14303, 14321, 14323, 14327, 14341, 14347, 14369, 14387, 14389, 14401, 14407, 14411, 14419, 14423, 14431, 14437, 14447, 14449, 14461, 14479, 14489, 14503, 14519, 14533, 14537, 14543, 14549, 14551, 14557, 14561, 14563, 14591, 14593, 14621, 14627, 14629, 14633, 14639, 14653, 14657, 14669, 14683, 14699, 14713, 14717, 14723, 14731, 14737, 14741, 14747, 14753, 14759]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_14153, by decide, by decide⟩,
    ⟨prime_14159, by decide, by decide⟩,
    ⟨prime_14173, by decide, by decide⟩,
    ⟨prime_14177, by decide, by decide⟩,
    ⟨prime_14197, by decide, by decide⟩,
    ⟨prime_14207, by decide, by decide⟩,
    ⟨prime_14221, by decide, by decide⟩,
    ⟨prime_14243, by decide, by decide⟩,
    ⟨prime_14249, by decide, by decide⟩,
    ⟨prime_14251, by decide, by decide⟩,
    ⟨prime_14281, by decide, by decide⟩,
    ⟨prime_14293, by decide, by decide⟩,
    ⟨prime_14303, by decide, by decide⟩,
    ⟨prime_14321, by decide, by decide⟩,
    ⟨prime_14323, by decide, by decide⟩,
    ⟨prime_14327, by decide, by decide⟩,
    ⟨prime_14341, by decide, by decide⟩,
    ⟨prime_14347, by decide, by decide⟩,
    ⟨prime_14369, by decide, by decide⟩,
    ⟨prime_14387, by decide, by decide⟩,
    ⟨prime_14389, by decide, by decide⟩,
    ⟨prime_14401, by decide, by decide⟩,
    ⟨prime_14407, by decide, by decide⟩,
    ⟨prime_14411, by decide, by decide⟩,
    ⟨prime_14419, by decide, by decide⟩,
    ⟨prime_14423, by decide, by decide⟩,
    ⟨prime_14431, by decide, by decide⟩,
    ⟨prime_14437, by decide, by decide⟩,
    ⟨prime_14447, by decide, by decide⟩,
    ⟨prime_14449, by decide, by decide⟩,
    ⟨prime_14461, by decide, by decide⟩,
    ⟨prime_14479, by decide, by decide⟩,
    ⟨prime_14489, by decide, by decide⟩,
    ⟨prime_14503, by decide, by decide⟩,
    ⟨prime_14519, by decide, by decide⟩,
    ⟨prime_14533, by decide, by decide⟩,
    ⟨prime_14537, by decide, by decide⟩,
    ⟨prime_14543, by decide, by decide⟩,
    ⟨prime_14549, by decide, by decide⟩,
    ⟨prime_14551, by decide, by decide⟩,
    ⟨prime_14557, by decide, by decide⟩,
    ⟨prime_14561, by decide, by decide⟩,
    ⟨prime_14563, by decide, by decide⟩,
    ⟨prime_14591, by decide, by decide⟩,
    ⟨prime_14593, by decide, by decide⟩,
    ⟨prime_14621, by decide, by decide⟩,
    ⟨prime_14627, by decide, by decide⟩,
    ⟨prime_14629, by decide, by decide⟩,
    ⟨prime_14633, by decide, by decide⟩,
    ⟨prime_14639, by decide, by decide⟩,
    ⟨prime_14653, by decide, by decide⟩,
    ⟨prime_14657, by decide, by decide⟩,
    ⟨prime_14669, by decide, by decide⟩,
    ⟨prime_14683, by decide, by decide⟩,
    ⟨prime_14699, by decide, by decide⟩,
    ⟨prime_14713, by decide, by decide⟩,
    ⟨prime_14717, by decide, by decide⟩,
    ⟨prime_14723, by decide, by decide⟩,
    ⟨prime_14731, by decide, by decide⟩,
    ⟨prime_14737, by decide, by decide⟩,
    ⟨prime_14741, by decide, by decide⟩,
    ⟨prime_14747, by decide, by decide⟩,
    ⟨prime_14753, by decide, by decide⟩,
    ⟨prime_14759, by decide, by decide⟩
  ⟩

end B026
end Sude.Lucas.Generated
