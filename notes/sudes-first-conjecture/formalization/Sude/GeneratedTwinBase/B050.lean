import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0074
import Sude.GeneratedFTT.N0086
import Sude.GeneratedFTT.N0090
import Sude.GeneratedFTT.N0101
import Sude.GeneratedFTT.N0104
import Sude.GeneratedFTT.N0113
import Sude.GeneratedFTT.N0120
import Sude.GeneratedFTT.N0128
import Sude.GeneratedFTT.N0131
import Sude.GeneratedFTT.N0139
import Sude.GeneratedTwinBase.M003
import Sude.GeneratedTwinBase.B048

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B050
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [29473, 29483, 29501, 29527, 29531, 29537, 29567, 29569, 29573, 29581, 29587, 29599, 29611, 29629, 29633, 29641, 29663, 29669, 29671, 29683, 29717, 29723, 29741, 29753, 29759, 29761, 29789, 29803, 29819, 29833, 29837, 29851, 29863, 29867, 29873, 29879, 29881, 29917, 29921, 29927, 29947, 29959, 29983, 29989, 30011, 30013, 30029, 30047, 30059, 30071, 30089, 30091, 30097, 30103, 30109, 30113, 30119, 30133, 30137, 30139, 30161, 30169, 30181, 30187]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_29473, by decide, by decide⟩,
    ⟨prime_29483, by decide, by decide⟩,
    ⟨prime_29501, by decide, by decide⟩,
    ⟨prime_29527, by decide, by decide⟩,
    ⟨prime_29531, by decide, by decide⟩,
    ⟨prime_29537, by decide, by decide⟩,
    ⟨prime_29567, by decide, by decide⟩,
    ⟨prime_29569, by decide, by decide⟩,
    ⟨prime_29573, by decide, by decide⟩,
    ⟨prime_29581, by decide, by decide⟩,
    ⟨prime_29587, by decide, by decide⟩,
    ⟨prime_29599, by decide, by decide⟩,
    ⟨prime_29611, by decide, by decide⟩,
    ⟨prime_29629, by decide, by decide⟩,
    ⟨prime_29633, by decide, by decide⟩,
    ⟨prime_29641, by decide, by decide⟩,
    ⟨prime_29663, by decide, by decide⟩,
    ⟨prime_29669, by decide, by decide⟩,
    ⟨prime_29671, by decide, by decide⟩,
    ⟨prime_29683, by decide, by decide⟩,
    ⟨prime_29717, by decide, by decide⟩,
    ⟨prime_29723, by decide, by decide⟩,
    ⟨prime_29741, by decide, by decide⟩,
    ⟨prime_29753, by decide, by decide⟩,
    ⟨prime_29759, by decide, by decide⟩,
    ⟨prime_29761, by decide, by decide⟩,
    ⟨prime_29789, by decide, by decide⟩,
    ⟨prime_29803, by decide, by decide⟩,
    ⟨prime_29819, by decide, by decide⟩,
    ⟨prime_29833, by decide, by decide⟩,
    ⟨prime_29837, by decide, by decide⟩,
    ⟨prime_29851, by decide, by decide⟩,
    ⟨prime_29863, by decide, by decide⟩,
    ⟨prime_29867, by decide, by decide⟩,
    ⟨prime_29873, by decide, by decide⟩,
    ⟨prime_29879, by decide, by decide⟩,
    ⟨prime_29881, by decide, by decide⟩,
    ⟨prime_29917, by decide, by decide⟩,
    ⟨prime_29921, by decide, by decide⟩,
    ⟨prime_29927, by decide, by decide⟩,
    ⟨prime_29947, by decide, by decide⟩,
    ⟨prime_29959, by decide, by decide⟩,
    ⟨prime_29983, by decide, by decide⟩,
    ⟨prime_29989, by decide, by decide⟩,
    ⟨prime_30011, by decide, by decide⟩,
    ⟨prime_30013, by decide, by decide⟩,
    ⟨prime_30029, by decide, by decide⟩,
    ⟨prime_30047, by decide, by decide⟩,
    ⟨prime_30059, by decide, by decide⟩,
    ⟨prime_30071, by decide, by decide⟩,
    ⟨prime_30089, by decide, by decide⟩,
    ⟨prime_30091, by decide, by decide⟩,
    ⟨prime_30097, by decide, by decide⟩,
    ⟨prime_30103, by decide, by decide⟩,
    ⟨prime_30109, by decide, by decide⟩,
    ⟨prime_30113, by decide, by decide⟩,
    ⟨prime_30119, by decide, by decide⟩,
    ⟨prime_30133, by decide, by decide⟩,
    ⟨prime_30137, by decide, by decide⟩,
    ⟨prime_30139, by decide, by decide⟩,
    ⟨prime_30161, by decide, by decide⟩,
    ⟨prime_30169, by decide, by decide⟩,
    ⟨prime_30181, by decide, by decide⟩,
    ⟨prime_30187, by decide, by decide⟩
  ⟩

end B050
end Sude.Lucas.Generated
