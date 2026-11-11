import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0064
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0075
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0080
import Sude.GeneratedFTT.N0085
import Sude.GeneratedFTT.N0090
import Sude.GeneratedFTT.N0091
import Sude.GeneratedFTT.N0092
import Sude.GeneratedFTT.N0095
import Sude.GeneratedFTT.N0099
import Sude.GeneratedFTT.N0105
import Sude.GeneratedFTT.N0108
import Sude.GeneratedFTT.N0113
import Sude.GeneratedFTT.N0139
import Sude.GeneratedFTT.N0147
import Sude.GeneratedFTT.N0150
import Sude.GeneratedTwinBase.M000
import Sude.GeneratedTwinBase.B017

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B019
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [9871, 9883, 9887, 9901, 9907, 9923, 9929, 9931, 9941, 9949, 9967, 9973, 10007, 10009, 10037, 10039, 10061, 10067, 10069, 10079, 10091, 10093, 10099, 10103, 10111, 10133, 10139, 10141, 10151, 10159, 10163, 10169, 10177, 10181, 10193, 10211, 10223, 10243, 10247, 10253, 10259, 10267, 10271, 10273, 10289, 10301, 10303, 10313, 10321, 10331, 10333, 10337, 10343, 10357, 10369, 10391, 10399, 10427, 10429, 10433, 10453, 10457, 10459, 10463]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_9871, by decide, by decide⟩,
    ⟨prime_9883, by decide, by decide⟩,
    ⟨prime_9887, by decide, by decide⟩,
    ⟨prime_9901, by decide, by decide⟩,
    ⟨prime_9907, by decide, by decide⟩,
    ⟨prime_9923, by decide, by decide⟩,
    ⟨prime_9929, by decide, by decide⟩,
    ⟨prime_9931, by decide, by decide⟩,
    ⟨prime_9941, by decide, by decide⟩,
    ⟨prime_9949, by decide, by decide⟩,
    ⟨prime_9967, by decide, by decide⟩,
    ⟨prime_9973, by decide, by decide⟩,
    ⟨prime_10007, by decide, by decide⟩,
    ⟨prime_10009, by decide, by decide⟩,
    ⟨prime_10037, by decide, by decide⟩,
    ⟨prime_10039, by decide, by decide⟩,
    ⟨prime_10061, by decide, by decide⟩,
    ⟨prime_10067, by decide, by decide⟩,
    ⟨prime_10069, by decide, by decide⟩,
    ⟨prime_10079, by decide, by decide⟩,
    ⟨prime_10091, by decide, by decide⟩,
    ⟨prime_10093, by decide, by decide⟩,
    ⟨prime_10099, by decide, by decide⟩,
    ⟨prime_10103, by decide, by decide⟩,
    ⟨prime_10111, by decide, by decide⟩,
    ⟨prime_10133, by decide, by decide⟩,
    ⟨prime_10139, by decide, by decide⟩,
    ⟨prime_10141, by decide, by decide⟩,
    ⟨prime_10151, by decide, by decide⟩,
    ⟨prime_10159, by decide, by decide⟩,
    ⟨prime_10163, by decide, by decide⟩,
    ⟨prime_10169, by decide, by decide⟩,
    ⟨prime_10177, by decide, by decide⟩,
    ⟨prime_10181, by decide, by decide⟩,
    ⟨prime_10193, by decide, by decide⟩,
    ⟨prime_10211, by decide, by decide⟩,
    ⟨prime_10223, by decide, by decide⟩,
    ⟨prime_10243, by decide, by decide⟩,
    ⟨prime_10247, by decide, by decide⟩,
    ⟨prime_10253, by decide, by decide⟩,
    ⟨prime_10259, by decide, by decide⟩,
    ⟨prime_10267, by decide, by decide⟩,
    ⟨prime_10271, by decide, by decide⟩,
    ⟨prime_10273, by decide, by decide⟩,
    ⟨prime_10289, by decide, by decide⟩,
    ⟨prime_10301, by decide, by decide⟩,
    ⟨prime_10303, by decide, by decide⟩,
    ⟨prime_10313, by decide, by decide⟩,
    ⟨prime_10321, by decide, by decide⟩,
    ⟨prime_10331, by decide, by decide⟩,
    ⟨prime_10333, by decide, by decide⟩,
    ⟨prime_10337, by decide, by decide⟩,
    ⟨prime_10343, by decide, by decide⟩,
    ⟨prime_10357, by decide, by decide⟩,
    ⟨prime_10369, by decide, by decide⟩,
    ⟨prime_10391, by decide, by decide⟩,
    ⟨prime_10399, by decide, by decide⟩,
    ⟨prime_10427, by decide, by decide⟩,
    ⟨prime_10429, by decide, by decide⟩,
    ⟨prime_10433, by decide, by decide⟩,
    ⟨prime_10453, by decide, by decide⟩,
    ⟨prime_10457, by decide, by decide⟩,
    ⟨prime_10459, by decide, by decide⟩,
    ⟨prime_10463, by decide, by decide⟩
  ⟩

end B019
end Sude.Lucas.Generated
