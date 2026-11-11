import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0064
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0079
import Sude.GeneratedFTT.N0080
import Sude.GeneratedFTT.N0082
import Sude.GeneratedFTT.N0090
import Sude.GeneratedFTT.N0098
import Sude.GeneratedFTT.N0099
import Sude.GeneratedFTT.N0100
import Sude.GeneratedFTT.N0107
import Sude.GeneratedFTT.N0109
import Sude.GeneratedFTT.N0113
import Sude.GeneratedFTT.N0117
import Sude.GeneratedFTT.N0124
import Sude.GeneratedFTT.N0125
import Sude.GeneratedFTT.N0132
import Sude.GeneratedFTT.N0138
import Sude.GeneratedFTT.N0149
import Sude.GeneratedTwinBase.M000
import Sude.GeneratedTwinBase.B031

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B033
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [18451, 18457, 18461, 18481, 18493, 18503, 18517, 18521, 18523, 18539, 18541, 18553, 18583, 18587, 18593, 18617, 18637, 18661, 18671, 18679, 18691, 18701, 18713, 18719, 18731, 18743, 18749, 18757, 18773, 18787, 18793, 18797, 18803, 18839, 18859, 18869, 18899, 18911, 18913, 18917, 18919, 18947, 18959, 18973, 18979, 19001, 19009, 19013, 19031, 19037, 19051, 19069, 19073, 19079, 19081, 19087, 19121, 19139, 19141, 19157, 19163, 19181, 19183, 19207]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_18451, by decide, by decide⟩,
    ⟨prime_18457, by decide, by decide⟩,
    ⟨prime_18461, by decide, by decide⟩,
    ⟨prime_18481, by decide, by decide⟩,
    ⟨prime_18493, by decide, by decide⟩,
    ⟨prime_18503, by decide, by decide⟩,
    ⟨prime_18517, by decide, by decide⟩,
    ⟨prime_18521, by decide, by decide⟩,
    ⟨prime_18523, by decide, by decide⟩,
    ⟨prime_18539, by decide, by decide⟩,
    ⟨prime_18541, by decide, by decide⟩,
    ⟨prime_18553, by decide, by decide⟩,
    ⟨prime_18583, by decide, by decide⟩,
    ⟨prime_18587, by decide, by decide⟩,
    ⟨prime_18593, by decide, by decide⟩,
    ⟨prime_18617, by decide, by decide⟩,
    ⟨prime_18637, by decide, by decide⟩,
    ⟨prime_18661, by decide, by decide⟩,
    ⟨prime_18671, by decide, by decide⟩,
    ⟨prime_18679, by decide, by decide⟩,
    ⟨prime_18691, by decide, by decide⟩,
    ⟨prime_18701, by decide, by decide⟩,
    ⟨prime_18713, by decide, by decide⟩,
    ⟨prime_18719, by decide, by decide⟩,
    ⟨prime_18731, by decide, by decide⟩,
    ⟨prime_18743, by decide, by decide⟩,
    ⟨prime_18749, by decide, by decide⟩,
    ⟨prime_18757, by decide, by decide⟩,
    ⟨prime_18773, by decide, by decide⟩,
    ⟨prime_18787, by decide, by decide⟩,
    ⟨prime_18793, by decide, by decide⟩,
    ⟨prime_18797, by decide, by decide⟩,
    ⟨prime_18803, by decide, by decide⟩,
    ⟨prime_18839, by decide, by decide⟩,
    ⟨prime_18859, by decide, by decide⟩,
    ⟨prime_18869, by decide, by decide⟩,
    ⟨prime_18899, by decide, by decide⟩,
    ⟨prime_18911, by decide, by decide⟩,
    ⟨prime_18913, by decide, by decide⟩,
    ⟨prime_18917, by decide, by decide⟩,
    ⟨prime_18919, by decide, by decide⟩,
    ⟨prime_18947, by decide, by decide⟩,
    ⟨prime_18959, by decide, by decide⟩,
    ⟨prime_18973, by decide, by decide⟩,
    ⟨prime_18979, by decide, by decide⟩,
    ⟨prime_19001, by decide, by decide⟩,
    ⟨prime_19009, by decide, by decide⟩,
    ⟨prime_19013, by decide, by decide⟩,
    ⟨prime_19031, by decide, by decide⟩,
    ⟨prime_19037, by decide, by decide⟩,
    ⟨prime_19051, by decide, by decide⟩,
    ⟨prime_19069, by decide, by decide⟩,
    ⟨prime_19073, by decide, by decide⟩,
    ⟨prime_19079, by decide, by decide⟩,
    ⟨prime_19081, by decide, by decide⟩,
    ⟨prime_19087, by decide, by decide⟩,
    ⟨prime_19121, by decide, by decide⟩,
    ⟨prime_19139, by decide, by decide⟩,
    ⟨prime_19141, by decide, by decide⟩,
    ⟨prime_19157, by decide, by decide⟩,
    ⟨prime_19163, by decide, by decide⟩,
    ⟨prime_19181, by decide, by decide⟩,
    ⟨prime_19183, by decide, by decide⟩,
    ⟨prime_19207, by decide, by decide⟩
  ⟩

end B033
end Sude.Lucas.Generated
