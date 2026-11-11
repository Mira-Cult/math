import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0078
import Sude.GeneratedFTT.N0079
import Sude.GeneratedFTT.N0080
import Sude.GeneratedFTT.N0084
import Sude.GeneratedFTT.N0085
import Sude.GeneratedFTT.N0086
import Sude.GeneratedFTT.N0091
import Sude.GeneratedFTT.N0098
import Sude.GeneratedFTT.N0101
import Sude.GeneratedFTT.N0104
import Sude.GeneratedFTT.N0108
import Sude.GeneratedFTT.N0109
import Sude.GeneratedFTT.N0116
import Sude.GeneratedFTT.N0132
import Sude.GeneratedFTT.N0135
import Sude.GeneratedFTT.N0142
import Sude.GeneratedFTT.N0145
import Sude.GeneratedFTT.N0146
import Sude.GeneratedTwinBase.M000
import Sude.GeneratedTwinBase.B025

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B027
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [14767, 14771, 14779, 14783, 14797, 14813, 14821, 14827, 14831, 14843, 14851, 14867, 14869, 14879, 14887, 14891, 14897, 14923, 14929, 14939, 14947, 14951, 14957, 14969, 14983, 15013, 15017, 15031, 15053, 15061, 15073, 15077, 15083, 15091, 15101, 15107, 15121, 15131, 15137, 15139, 15149, 15161, 15173, 15187, 15193, 15199, 15217, 15227, 15233, 15241, 15259, 15263, 15269, 15271, 15277, 15287, 15289, 15299, 15307, 15313, 15319, 15329, 15331, 15349]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_14767, by decide, by decide⟩,
    ⟨prime_14771, by decide, by decide⟩,
    ⟨prime_14779, by decide, by decide⟩,
    ⟨prime_14783, by decide, by decide⟩,
    ⟨prime_14797, by decide, by decide⟩,
    ⟨prime_14813, by decide, by decide⟩,
    ⟨prime_14821, by decide, by decide⟩,
    ⟨prime_14827, by decide, by decide⟩,
    ⟨prime_14831, by decide, by decide⟩,
    ⟨prime_14843, by decide, by decide⟩,
    ⟨prime_14851, by decide, by decide⟩,
    ⟨prime_14867, by decide, by decide⟩,
    ⟨prime_14869, by decide, by decide⟩,
    ⟨prime_14879, by decide, by decide⟩,
    ⟨prime_14887, by decide, by decide⟩,
    ⟨prime_14891, by decide, by decide⟩,
    ⟨prime_14897, by decide, by decide⟩,
    ⟨prime_14923, by decide, by decide⟩,
    ⟨prime_14929, by decide, by decide⟩,
    ⟨prime_14939, by decide, by decide⟩,
    ⟨prime_14947, by decide, by decide⟩,
    ⟨prime_14951, by decide, by decide⟩,
    ⟨prime_14957, by decide, by decide⟩,
    ⟨prime_14969, by decide, by decide⟩,
    ⟨prime_14983, by decide, by decide⟩,
    ⟨prime_15013, by decide, by decide⟩,
    ⟨prime_15017, by decide, by decide⟩,
    ⟨prime_15031, by decide, by decide⟩,
    ⟨prime_15053, by decide, by decide⟩,
    ⟨prime_15061, by decide, by decide⟩,
    ⟨prime_15073, by decide, by decide⟩,
    ⟨prime_15077, by decide, by decide⟩,
    ⟨prime_15083, by decide, by decide⟩,
    ⟨prime_15091, by decide, by decide⟩,
    ⟨prime_15101, by decide, by decide⟩,
    ⟨prime_15107, by decide, by decide⟩,
    ⟨prime_15121, by decide, by decide⟩,
    ⟨prime_15131, by decide, by decide⟩,
    ⟨prime_15137, by decide, by decide⟩,
    ⟨prime_15139, by decide, by decide⟩,
    ⟨prime_15149, by decide, by decide⟩,
    ⟨prime_15161, by decide, by decide⟩,
    ⟨prime_15173, by decide, by decide⟩,
    ⟨prime_15187, by decide, by decide⟩,
    ⟨prime_15193, by decide, by decide⟩,
    ⟨prime_15199, by decide, by decide⟩,
    ⟨prime_15217, by decide, by decide⟩,
    ⟨prime_15227, by decide, by decide⟩,
    ⟨prime_15233, by decide, by decide⟩,
    ⟨prime_15241, by decide, by decide⟩,
    ⟨prime_15259, by decide, by decide⟩,
    ⟨prime_15263, by decide, by decide⟩,
    ⟨prime_15269, by decide, by decide⟩,
    ⟨prime_15271, by decide, by decide⟩,
    ⟨prime_15277, by decide, by decide⟩,
    ⟨prime_15287, by decide, by decide⟩,
    ⟨prime_15289, by decide, by decide⟩,
    ⟨prime_15299, by decide, by decide⟩,
    ⟨prime_15307, by decide, by decide⟩,
    ⟨prime_15313, by decide, by decide⟩,
    ⟨prime_15319, by decide, by decide⟩,
    ⟨prime_15329, by decide, by decide⟩,
    ⟨prime_15331, by decide, by decide⟩,
    ⟨prime_15349, by decide, by decide⟩
  ⟩

end B027
end Sude.Lucas.Generated
