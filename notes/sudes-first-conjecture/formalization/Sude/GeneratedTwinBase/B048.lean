import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0075
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0081
import Sude.GeneratedFTT.N0095
import Sude.GeneratedFTT.N0097
import Sude.GeneratedFTT.N0100
import Sude.GeneratedFTT.N0101
import Sude.GeneratedFTT.N0102
import Sude.GeneratedFTT.N0115
import Sude.GeneratedFTT.N0117
import Sude.GeneratedFTT.N0121
import Sude.GeneratedFTT.N0131
import Sude.GeneratedFTT.N0137
import Sude.GeneratedFTT.N0141
import Sude.GeneratedFTT.N0148
import Sude.GeneratedFTT.N0149
import Sude.GeneratedTwinBase.M003
import Sude.GeneratedTwinBase.B046

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B048
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [28201, 28211, 28219, 28229, 28277, 28279, 28283, 28289, 28297, 28307, 28309, 28319, 28349, 28351, 28387, 28393, 28403, 28409, 28411, 28429, 28433, 28439, 28447, 28463, 28477, 28493, 28499, 28513, 28517, 28537, 28541, 28547, 28549, 28559, 28571, 28573, 28579, 28591, 28597, 28603, 28607, 28619, 28621, 28627, 28631, 28643, 28649, 28657, 28661, 28663, 28669, 28687, 28697, 28703, 28711, 28723, 28729, 28751, 28753, 28759, 28771, 28789, 28793, 28807]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_28201, by decide, by decide⟩,
    ⟨prime_28211, by decide, by decide⟩,
    ⟨prime_28219, by decide, by decide⟩,
    ⟨prime_28229, by decide, by decide⟩,
    ⟨prime_28277, by decide, by decide⟩,
    ⟨prime_28279, by decide, by decide⟩,
    ⟨prime_28283, by decide, by decide⟩,
    ⟨prime_28289, by decide, by decide⟩,
    ⟨prime_28297, by decide, by decide⟩,
    ⟨prime_28307, by decide, by decide⟩,
    ⟨prime_28309, by decide, by decide⟩,
    ⟨prime_28319, by decide, by decide⟩,
    ⟨prime_28349, by decide, by decide⟩,
    ⟨prime_28351, by decide, by decide⟩,
    ⟨prime_28387, by decide, by decide⟩,
    ⟨prime_28393, by decide, by decide⟩,
    ⟨prime_28403, by decide, by decide⟩,
    ⟨prime_28409, by decide, by decide⟩,
    ⟨prime_28411, by decide, by decide⟩,
    ⟨prime_28429, by decide, by decide⟩,
    ⟨prime_28433, by decide, by decide⟩,
    ⟨prime_28439, by decide, by decide⟩,
    ⟨prime_28447, by decide, by decide⟩,
    ⟨prime_28463, by decide, by decide⟩,
    ⟨prime_28477, by decide, by decide⟩,
    ⟨prime_28493, by decide, by decide⟩,
    ⟨prime_28499, by decide, by decide⟩,
    ⟨prime_28513, by decide, by decide⟩,
    ⟨prime_28517, by decide, by decide⟩,
    ⟨prime_28537, by decide, by decide⟩,
    ⟨prime_28541, by decide, by decide⟩,
    ⟨prime_28547, by decide, by decide⟩,
    ⟨prime_28549, by decide, by decide⟩,
    ⟨prime_28559, by decide, by decide⟩,
    ⟨prime_28571, by decide, by decide⟩,
    ⟨prime_28573, by decide, by decide⟩,
    ⟨prime_28579, by decide, by decide⟩,
    ⟨prime_28591, by decide, by decide⟩,
    ⟨prime_28597, by decide, by decide⟩,
    ⟨prime_28603, by decide, by decide⟩,
    ⟨prime_28607, by decide, by decide⟩,
    ⟨prime_28619, by decide, by decide⟩,
    ⟨prime_28621, by decide, by decide⟩,
    ⟨prime_28627, by decide, by decide⟩,
    ⟨prime_28631, by decide, by decide⟩,
    ⟨prime_28643, by decide, by decide⟩,
    ⟨prime_28649, by decide, by decide⟩,
    ⟨prime_28657, by decide, by decide⟩,
    ⟨prime_28661, by decide, by decide⟩,
    ⟨prime_28663, by decide, by decide⟩,
    ⟨prime_28669, by decide, by decide⟩,
    ⟨prime_28687, by decide, by decide⟩,
    ⟨prime_28697, by decide, by decide⟩,
    ⟨prime_28703, by decide, by decide⟩,
    ⟨prime_28711, by decide, by decide⟩,
    ⟨prime_28723, by decide, by decide⟩,
    ⟨prime_28729, by decide, by decide⟩,
    ⟨prime_28751, by decide, by decide⟩,
    ⟨prime_28753, by decide, by decide⟩,
    ⟨prime_28759, by decide, by decide⟩,
    ⟨prime_28771, by decide, by decide⟩,
    ⟨prime_28789, by decide, by decide⟩,
    ⟨prime_28793, by decide, by decide⟩,
    ⟨prime_28807, by decide, by decide⟩
  ⟩

end B048
end Sude.Lucas.Generated
