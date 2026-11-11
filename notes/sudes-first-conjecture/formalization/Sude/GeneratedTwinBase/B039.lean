import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0064
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0074
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0089
import Sude.GeneratedFTT.N0095
import Sude.GeneratedFTT.N0105
import Sude.GeneratedFTT.N0110
import Sude.GeneratedFTT.N0111
import Sude.GeneratedFTT.N0112
import Sude.GeneratedFTT.N0127
import Sude.GeneratedFTT.N0133
import Sude.GeneratedFTT.N0135
import Sude.GeneratedFTT.N0139
import Sude.GeneratedFTT.N0141
import Sude.GeneratedFTT.N0148
import Sude.GeneratedTwinBase.M001
import Sude.GeneratedTwinBase.B037

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B039
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [22291, 22303, 22307, 22343, 22349, 22367, 22369, 22381, 22391, 22397, 22409, 22433, 22441, 22447, 22453, 22469, 22481, 22483, 22501, 22511, 22531, 22541, 22543, 22549, 22567, 22571, 22573, 22613, 22619, 22621, 22637, 22639, 22643, 22651, 22669, 22679, 22691, 22697, 22699, 22709, 22717, 22721, 22727, 22739, 22741, 22751, 22769, 22777, 22783, 22787, 22807, 22811, 22817, 22853, 22859, 22861, 22871, 22877, 22901, 22907, 22921, 22937, 22943, 22961]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_22291, by decide, by decide⟩,
    ⟨prime_22303, by decide, by decide⟩,
    ⟨prime_22307, by decide, by decide⟩,
    ⟨prime_22343, by decide, by decide⟩,
    ⟨prime_22349, by decide, by decide⟩,
    ⟨prime_22367, by decide, by decide⟩,
    ⟨prime_22369, by decide, by decide⟩,
    ⟨prime_22381, by decide, by decide⟩,
    ⟨prime_22391, by decide, by decide⟩,
    ⟨prime_22397, by decide, by decide⟩,
    ⟨prime_22409, by decide, by decide⟩,
    ⟨prime_22433, by decide, by decide⟩,
    ⟨prime_22441, by decide, by decide⟩,
    ⟨prime_22447, by decide, by decide⟩,
    ⟨prime_22453, by decide, by decide⟩,
    ⟨prime_22469, by decide, by decide⟩,
    ⟨prime_22481, by decide, by decide⟩,
    ⟨prime_22483, by decide, by decide⟩,
    ⟨prime_22501, by decide, by decide⟩,
    ⟨prime_22511, by decide, by decide⟩,
    ⟨prime_22531, by decide, by decide⟩,
    ⟨prime_22541, by decide, by decide⟩,
    ⟨prime_22543, by decide, by decide⟩,
    ⟨prime_22549, by decide, by decide⟩,
    ⟨prime_22567, by decide, by decide⟩,
    ⟨prime_22571, by decide, by decide⟩,
    ⟨prime_22573, by decide, by decide⟩,
    ⟨prime_22613, by decide, by decide⟩,
    ⟨prime_22619, by decide, by decide⟩,
    ⟨prime_22621, by decide, by decide⟩,
    ⟨prime_22637, by decide, by decide⟩,
    ⟨prime_22639, by decide, by decide⟩,
    ⟨prime_22643, by decide, by decide⟩,
    ⟨prime_22651, by decide, by decide⟩,
    ⟨prime_22669, by decide, by decide⟩,
    ⟨prime_22679, by decide, by decide⟩,
    ⟨prime_22691, by decide, by decide⟩,
    ⟨prime_22697, by decide, by decide⟩,
    ⟨prime_22699, by decide, by decide⟩,
    ⟨prime_22709, by decide, by decide⟩,
    ⟨prime_22717, by decide, by decide⟩,
    ⟨prime_22721, by decide, by decide⟩,
    ⟨prime_22727, by decide, by decide⟩,
    ⟨prime_22739, by decide, by decide⟩,
    ⟨prime_22741, by decide, by decide⟩,
    ⟨prime_22751, by decide, by decide⟩,
    ⟨prime_22769, by decide, by decide⟩,
    ⟨prime_22777, by decide, by decide⟩,
    ⟨prime_22783, by decide, by decide⟩,
    ⟨prime_22787, by decide, by decide⟩,
    ⟨prime_22807, by decide, by decide⟩,
    ⟨prime_22811, by decide, by decide⟩,
    ⟨prime_22817, by decide, by decide⟩,
    ⟨prime_22853, by decide, by decide⟩,
    ⟨prime_22859, by decide, by decide⟩,
    ⟨prime_22861, by decide, by decide⟩,
    ⟨prime_22871, by decide, by decide⟩,
    ⟨prime_22877, by decide, by decide⟩,
    ⟨prime_22901, by decide, by decide⟩,
    ⟨prime_22907, by decide, by decide⟩,
    ⟨prime_22921, by decide, by decide⟩,
    ⟨prime_22937, by decide, by decide⟩,
    ⟨prime_22943, by decide, by decide⟩,
    ⟨prime_22961, by decide, by decide⟩
  ⟩

end B039
end Sude.Lucas.Generated
