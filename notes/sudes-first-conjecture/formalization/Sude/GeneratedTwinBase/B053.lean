import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0083
import Sude.GeneratedFTT.N0095
import Sude.GeneratedFTT.N0096
import Sude.GeneratedFTT.N0099
import Sude.GeneratedFTT.N0112
import Sude.GeneratedFTT.N0119
import Sude.GeneratedFTT.N0140
import Sude.GeneratedFTT.N0143
import Sude.GeneratedFTT.N0145
import Sude.GeneratedFTT.N0150
import Sude.GeneratedTwinBase.M003
import Sude.GeneratedTwinBase.M004
import Sude.GeneratedTwinBase.B051

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B053
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [31541, 31543, 31547, 31567, 31573, 31583, 31601, 31607, 31627, 31643, 31649, 31657, 31663, 31667, 31687, 31699, 31721, 31723, 31727, 31729, 31741, 31751, 31769, 31771, 31793, 31799, 31817, 31847, 31849, 31859, 31873, 31883, 31891, 31907, 31957, 31963, 31973, 31981, 31991, 32003, 32009, 32027, 32029, 32051, 32057, 32059, 32063, 32069, 32077, 32083, 32089, 32099, 32117, 32119, 32141, 32143, 32159, 32173, 32183, 32189, 32191, 32203, 32213, 32233]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_31541, by decide, by decide⟩,
    ⟨prime_31543, by decide, by decide⟩,
    ⟨prime_31547, by decide, by decide⟩,
    ⟨prime_31567, by decide, by decide⟩,
    ⟨prime_31573, by decide, by decide⟩,
    ⟨prime_31583, by decide, by decide⟩,
    ⟨prime_31601, by decide, by decide⟩,
    ⟨prime_31607, by decide, by decide⟩,
    ⟨prime_31627, by decide, by decide⟩,
    ⟨prime_31643, by decide, by decide⟩,
    ⟨prime_31649, by decide, by decide⟩,
    ⟨prime_31657, by decide, by decide⟩,
    ⟨prime_31663, by decide, by decide⟩,
    ⟨prime_31667, by decide, by decide⟩,
    ⟨prime_31687, by decide, by decide⟩,
    ⟨prime_31699, by decide, by decide⟩,
    ⟨prime_31721, by decide, by decide⟩,
    ⟨prime_31723, by decide, by decide⟩,
    ⟨prime_31727, by decide, by decide⟩,
    ⟨prime_31729, by decide, by decide⟩,
    ⟨prime_31741, by decide, by decide⟩,
    ⟨prime_31751, by decide, by decide⟩,
    ⟨prime_31769, by decide, by decide⟩,
    ⟨prime_31771, by decide, by decide⟩,
    ⟨prime_31793, by decide, by decide⟩,
    ⟨prime_31799, by decide, by decide⟩,
    ⟨prime_31817, by decide, by decide⟩,
    ⟨prime_31847, by decide, by decide⟩,
    ⟨prime_31849, by decide, by decide⟩,
    ⟨prime_31859, by decide, by decide⟩,
    ⟨prime_31873, by decide, by decide⟩,
    ⟨prime_31883, by decide, by decide⟩,
    ⟨prime_31891, by decide, by decide⟩,
    ⟨prime_31907, by decide, by decide⟩,
    ⟨prime_31957, by decide, by decide⟩,
    ⟨prime_31963, by decide, by decide⟩,
    ⟨prime_31973, by decide, by decide⟩,
    ⟨prime_31981, by decide, by decide⟩,
    ⟨prime_31991, by decide, by decide⟩,
    ⟨prime_32003, by decide, by decide⟩,
    ⟨prime_32009, by decide, by decide⟩,
    ⟨prime_32027, by decide, by decide⟩,
    ⟨prime_32029, by decide, by decide⟩,
    ⟨prime_32051, by decide, by decide⟩,
    ⟨prime_32057, by decide, by decide⟩,
    ⟨prime_32059, by decide, by decide⟩,
    ⟨prime_32063, by decide, by decide⟩,
    ⟨prime_32069, by decide, by decide⟩,
    ⟨prime_32077, by decide, by decide⟩,
    ⟨prime_32083, by decide, by decide⟩,
    ⟨prime_32089, by decide, by decide⟩,
    ⟨prime_32099, by decide, by decide⟩,
    ⟨prime_32117, by decide, by decide⟩,
    ⟨prime_32119, by decide, by decide⟩,
    ⟨prime_32141, by decide, by decide⟩,
    ⟨prime_32143, by decide, by decide⟩,
    ⟨prime_32159, by decide, by decide⟩,
    ⟨prime_32173, by decide, by decide⟩,
    ⟨prime_32183, by decide, by decide⟩,
    ⟨prime_32189, by decide, by decide⟩,
    ⟨prime_32191, by decide, by decide⟩,
    ⟨prime_32203, by decide, by decide⟩,
    ⟨prime_32213, by decide, by decide⟩,
    ⟨prime_32233, by decide, by decide⟩
  ⟩

end B053
end Sude.Lucas.Generated
