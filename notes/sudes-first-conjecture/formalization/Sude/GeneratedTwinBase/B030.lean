import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0053
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0081
import Sude.GeneratedFTT.N0082
import Sude.GeneratedFTT.N0084
import Sude.GeneratedFTT.N0087
import Sude.GeneratedFTT.N0088
import Sude.GeneratedFTT.N0096
import Sude.GeneratedFTT.N0099
import Sude.GeneratedFTT.N0103
import Sude.GeneratedFTT.N0115
import Sude.GeneratedFTT.N0125
import Sude.GeneratedFTT.N0127
import Sude.GeneratedFTT.N0133
import Sude.GeneratedFTT.N0140
import Sude.GeneratedTwinBase.M000
import Sude.GeneratedTwinBase.B028

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B030
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [16619, 16631, 16633, 16649, 16651, 16657, 16661, 16673, 16691, 16693, 16699, 16703, 16729, 16741, 16747, 16759, 16763, 16787, 16811, 16823, 16829, 16831, 16843, 16871, 16879, 16883, 16889, 16901, 16903, 16921, 16927, 16931, 16937, 16943, 16963, 16979, 16981, 16987, 16993, 17011, 17021, 17027, 17029, 17033, 17041, 17047, 17053, 17077, 17093, 17099, 17107, 17117, 17123, 17137, 17159, 17167, 17183, 17189, 17191, 17203, 17207, 17209, 17231, 17239]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_16619, by decide, by decide⟩,
    ⟨prime_16631, by decide, by decide⟩,
    ⟨prime_16633, by decide, by decide⟩,
    ⟨prime_16649, by decide, by decide⟩,
    ⟨prime_16651, by decide, by decide⟩,
    ⟨prime_16657, by decide, by decide⟩,
    ⟨prime_16661, by decide, by decide⟩,
    ⟨prime_16673, by decide, by decide⟩,
    ⟨prime_16691, by decide, by decide⟩,
    ⟨prime_16693, by decide, by decide⟩,
    ⟨prime_16699, by decide, by decide⟩,
    ⟨prime_16703, by decide, by decide⟩,
    ⟨prime_16729, by decide, by decide⟩,
    ⟨prime_16741, by decide, by decide⟩,
    ⟨prime_16747, by decide, by decide⟩,
    ⟨prime_16759, by decide, by decide⟩,
    ⟨prime_16763, by decide, by decide⟩,
    ⟨prime_16787, by decide, by decide⟩,
    ⟨prime_16811, by decide, by decide⟩,
    ⟨prime_16823, by decide, by decide⟩,
    ⟨prime_16829, by decide, by decide⟩,
    ⟨prime_16831, by decide, by decide⟩,
    ⟨prime_16843, by decide, by decide⟩,
    ⟨prime_16871, by decide, by decide⟩,
    ⟨prime_16879, by decide, by decide⟩,
    ⟨prime_16883, by decide, by decide⟩,
    ⟨prime_16889, by decide, by decide⟩,
    ⟨prime_16901, by decide, by decide⟩,
    ⟨prime_16903, by decide, by decide⟩,
    ⟨prime_16921, by decide, by decide⟩,
    ⟨prime_16927, by decide, by decide⟩,
    ⟨prime_16931, by decide, by decide⟩,
    ⟨prime_16937, by decide, by decide⟩,
    ⟨prime_16943, by decide, by decide⟩,
    ⟨prime_16963, by decide, by decide⟩,
    ⟨prime_16979, by decide, by decide⟩,
    ⟨prime_16981, by decide, by decide⟩,
    ⟨prime_16987, by decide, by decide⟩,
    ⟨prime_16993, by decide, by decide⟩,
    ⟨prime_17011, by decide, by decide⟩,
    ⟨prime_17021, by decide, by decide⟩,
    ⟨prime_17027, by decide, by decide⟩,
    ⟨prime_17029, by decide, by decide⟩,
    ⟨prime_17033, by decide, by decide⟩,
    ⟨prime_17041, by decide, by decide⟩,
    ⟨prime_17047, by decide, by decide⟩,
    ⟨prime_17053, by decide, by decide⟩,
    ⟨prime_17077, by decide, by decide⟩,
    ⟨prime_17093, by decide, by decide⟩,
    ⟨prime_17099, by decide, by decide⟩,
    ⟨prime_17107, by decide, by decide⟩,
    ⟨prime_17117, by decide, by decide⟩,
    ⟨prime_17123, by decide, by decide⟩,
    ⟨prime_17137, by decide, by decide⟩,
    ⟨prime_17159, by decide, by decide⟩,
    ⟨prime_17167, by decide, by decide⟩,
    ⟨prime_17183, by decide, by decide⟩,
    ⟨prime_17189, by decide, by decide⟩,
    ⟨prime_17191, by decide, by decide⟩,
    ⟨prime_17203, by decide, by decide⟩,
    ⟨prime_17207, by decide, by decide⟩,
    ⟨prime_17209, by decide, by decide⟩,
    ⟨prime_17231, by decide, by decide⟩,
    ⟨prime_17239, by decide, by decide⟩
  ⟩

end B030
end Sude.Lucas.Generated
