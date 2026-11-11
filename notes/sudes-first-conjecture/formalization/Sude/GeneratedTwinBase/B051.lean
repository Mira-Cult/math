import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0087
import Sude.GeneratedFTT.N0097
import Sude.GeneratedFTT.N0104
import Sude.GeneratedFTT.N0106
import Sude.GeneratedFTT.N0110
import Sude.GeneratedFTT.N0112
import Sude.GeneratedFTT.N0114
import Sude.GeneratedFTT.N0116
import Sude.GeneratedFTT.N0117
import Sude.GeneratedFTT.N0122
import Sude.GeneratedFTT.N0126
import Sude.GeneratedFTT.N0132
import Sude.GeneratedTwinBase.M003
import Sude.GeneratedTwinBase.B049

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B051
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [30197, 30203, 30211, 30223, 30241, 30253, 30259, 30269, 30271, 30293, 30307, 30313, 30319, 30323, 30341, 30347, 30367, 30389, 30391, 30403, 30427, 30431, 30449, 30467, 30469, 30491, 30493, 30497, 30509, 30517, 30529, 30539, 30553, 30557, 30559, 30577, 30593, 30631, 30637, 30643, 30649, 30661, 30671, 30677, 30689, 30697, 30703, 30707, 30713, 30727, 30757, 30763, 30773, 30781, 30803, 30809, 30817, 30829, 30839, 30841, 30851, 30853, 30859, 30869]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_30197, by decide, by decide⟩,
    ⟨prime_30203, by decide, by decide⟩,
    ⟨prime_30211, by decide, by decide⟩,
    ⟨prime_30223, by decide, by decide⟩,
    ⟨prime_30241, by decide, by decide⟩,
    ⟨prime_30253, by decide, by decide⟩,
    ⟨prime_30259, by decide, by decide⟩,
    ⟨prime_30269, by decide, by decide⟩,
    ⟨prime_30271, by decide, by decide⟩,
    ⟨prime_30293, by decide, by decide⟩,
    ⟨prime_30307, by decide, by decide⟩,
    ⟨prime_30313, by decide, by decide⟩,
    ⟨prime_30319, by decide, by decide⟩,
    ⟨prime_30323, by decide, by decide⟩,
    ⟨prime_30341, by decide, by decide⟩,
    ⟨prime_30347, by decide, by decide⟩,
    ⟨prime_30367, by decide, by decide⟩,
    ⟨prime_30389, by decide, by decide⟩,
    ⟨prime_30391, by decide, by decide⟩,
    ⟨prime_30403, by decide, by decide⟩,
    ⟨prime_30427, by decide, by decide⟩,
    ⟨prime_30431, by decide, by decide⟩,
    ⟨prime_30449, by decide, by decide⟩,
    ⟨prime_30467, by decide, by decide⟩,
    ⟨prime_30469, by decide, by decide⟩,
    ⟨prime_30491, by decide, by decide⟩,
    ⟨prime_30493, by decide, by decide⟩,
    ⟨prime_30497, by decide, by decide⟩,
    ⟨prime_30509, by decide, by decide⟩,
    ⟨prime_30517, by decide, by decide⟩,
    ⟨prime_30529, by decide, by decide⟩,
    ⟨prime_30539, by decide, by decide⟩,
    ⟨prime_30553, by decide, by decide⟩,
    ⟨prime_30557, by decide, by decide⟩,
    ⟨prime_30559, by decide, by decide⟩,
    ⟨prime_30577, by decide, by decide⟩,
    ⟨prime_30593, by decide, by decide⟩,
    ⟨prime_30631, by decide, by decide⟩,
    ⟨prime_30637, by decide, by decide⟩,
    ⟨prime_30643, by decide, by decide⟩,
    ⟨prime_30649, by decide, by decide⟩,
    ⟨prime_30661, by decide, by decide⟩,
    ⟨prime_30671, by decide, by decide⟩,
    ⟨prime_30677, by decide, by decide⟩,
    ⟨prime_30689, by decide, by decide⟩,
    ⟨prime_30697, by decide, by decide⟩,
    ⟨prime_30703, by decide, by decide⟩,
    ⟨prime_30707, by decide, by decide⟩,
    ⟨prime_30713, by decide, by decide⟩,
    ⟨prime_30727, by decide, by decide⟩,
    ⟨prime_30757, by decide, by decide⟩,
    ⟨prime_30763, by decide, by decide⟩,
    ⟨prime_30773, by decide, by decide⟩,
    ⟨prime_30781, by decide, by decide⟩,
    ⟨prime_30803, by decide, by decide⟩,
    ⟨prime_30809, by decide, by decide⟩,
    ⟨prime_30817, by decide, by decide⟩,
    ⟨prime_30829, by decide, by decide⟩,
    ⟨prime_30839, by decide, by decide⟩,
    ⟨prime_30841, by decide, by decide⟩,
    ⟨prime_30851, by decide, by decide⟩,
    ⟨prime_30853, by decide, by decide⟩,
    ⟨prime_30859, by decide, by decide⟩,
    ⟨prime_30869, by decide, by decide⟩
  ⟩

end B051
end Sude.Lucas.Generated
