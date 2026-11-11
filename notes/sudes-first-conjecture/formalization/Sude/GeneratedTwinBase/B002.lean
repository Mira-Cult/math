import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0027
import Sude.GeneratedTwinBase.B000

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B002
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_733, by decide, by decide⟩,
    ⟨prime_739, by decide, by decide⟩,
    ⟨prime_743, by decide, by decide⟩,
    ⟨prime_751, by decide, by decide⟩,
    ⟨prime_757, by decide, by decide⟩,
    ⟨prime_761, by decide, by decide⟩,
    ⟨prime_769, by decide, by decide⟩,
    ⟨prime_773, by decide, by decide⟩,
    ⟨prime_787, by decide, by decide⟩,
    ⟨prime_797, by decide, by decide⟩,
    ⟨prime_809, by decide, by decide⟩,
    ⟨prime_811, by decide, by decide⟩,
    ⟨prime_821, by decide, by decide⟩,
    ⟨prime_823, by decide, by decide⟩,
    ⟨prime_827, by decide, by decide⟩,
    ⟨prime_829, by decide, by decide⟩,
    ⟨prime_839, by decide, by decide⟩,
    ⟨prime_853, by decide, by decide⟩,
    ⟨prime_857, by decide, by decide⟩,
    ⟨prime_859, by decide, by decide⟩,
    ⟨prime_863, by decide, by decide⟩,
    ⟨prime_877, by decide, by decide⟩,
    ⟨prime_881, by decide, by decide⟩,
    ⟨prime_883, by decide, by decide⟩,
    ⟨prime_887, by decide, by decide⟩,
    ⟨prime_907, by decide, by decide⟩,
    ⟨prime_911, by decide, by decide⟩,
    ⟨prime_919, by decide, by decide⟩,
    ⟨prime_929, by decide, by decide⟩,
    ⟨prime_937, by decide, by decide⟩,
    ⟨prime_941, by decide, by decide⟩,
    ⟨prime_947, by decide, by decide⟩,
    ⟨prime_953, by decide, by decide⟩,
    ⟨prime_967, by decide, by decide⟩,
    ⟨prime_971, by decide, by decide⟩,
    ⟨prime_977, by decide, by decide⟩,
    ⟨prime_983, by decide, by decide⟩,
    ⟨prime_991, by decide, by decide⟩,
    ⟨prime_997, by decide, by decide⟩,
    ⟨prime_1009, by decide, by decide⟩,
    ⟨prime_1013, by decide, by decide⟩,
    ⟨prime_1019, by decide, by decide⟩,
    ⟨prime_1021, by decide, by decide⟩,
    ⟨prime_1031, by decide, by decide⟩,
    ⟨prime_1033, by decide, by decide⟩,
    ⟨prime_1039, by decide, by decide⟩,
    ⟨prime_1049, by decide, by decide⟩,
    ⟨prime_1051, by decide, by decide⟩,
    ⟨prime_1061, by decide, by decide⟩,
    ⟨prime_1063, by decide, by decide⟩,
    ⟨prime_1069, by decide, by decide⟩,
    ⟨prime_1087, by decide, by decide⟩,
    ⟨prime_1091, by decide, by decide⟩,
    ⟨prime_1093, by decide, by decide⟩,
    ⟨prime_1097, by decide, by decide⟩,
    ⟨prime_1103, by decide, by decide⟩,
    ⟨prime_1109, by decide, by decide⟩,
    ⟨prime_1117, by decide, by decide⟩,
    ⟨prime_1123, by decide, by decide⟩,
    ⟨prime_1129, by decide, by decide⟩,
    ⟨prime_1151, by decide, by decide⟩,
    ⟨prime_1153, by decide, by decide⟩,
    ⟨prime_1163, by decide, by decide⟩,
    ⟨prime_1171, by decide, by decide⟩
  ⟩

end B002
end Sude.Lucas.Generated
