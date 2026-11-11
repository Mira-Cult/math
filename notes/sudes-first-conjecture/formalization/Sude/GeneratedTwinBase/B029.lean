import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0053
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0082
import Sude.GeneratedFTT.N0087
import Sude.GeneratedFTT.N0090
import Sude.GeneratedFTT.N0093
import Sude.GeneratedFTT.N0107
import Sude.GeneratedFTT.N0109
import Sude.GeneratedFTT.N0110
import Sude.GeneratedFTT.N0111
import Sude.GeneratedFTT.N0114
import Sude.GeneratedFTT.N0119
import Sude.GeneratedFTT.N0122
import Sude.GeneratedFTT.N0134
import Sude.GeneratedFTT.N0138
import Sude.GeneratedFTT.N0143
import Sude.GeneratedTwinBase.M000
import Sude.GeneratedTwinBase.B027

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B029
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [15937, 15959, 15971, 15973, 15991, 16001, 16007, 16033, 16057, 16061, 16063, 16067, 16069, 16073, 16087, 16091, 16097, 16103, 16111, 16127, 16139, 16141, 16183, 16187, 16189, 16193, 16217, 16223, 16229, 16231, 16249, 16253, 16267, 16273, 16301, 16319, 16333, 16339, 16349, 16361, 16363, 16369, 16381, 16411, 16417, 16421, 16427, 16433, 16447, 16451, 16453, 16477, 16481, 16487, 16493, 16519, 16529, 16547, 16553, 16561, 16567, 16573, 16603, 16607]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_15937, by decide, by decide⟩,
    ⟨prime_15959, by decide, by decide⟩,
    ⟨prime_15971, by decide, by decide⟩,
    ⟨prime_15973, by decide, by decide⟩,
    ⟨prime_15991, by decide, by decide⟩,
    ⟨prime_16001, by decide, by decide⟩,
    ⟨prime_16007, by decide, by decide⟩,
    ⟨prime_16033, by decide, by decide⟩,
    ⟨prime_16057, by decide, by decide⟩,
    ⟨prime_16061, by decide, by decide⟩,
    ⟨prime_16063, by decide, by decide⟩,
    ⟨prime_16067, by decide, by decide⟩,
    ⟨prime_16069, by decide, by decide⟩,
    ⟨prime_16073, by decide, by decide⟩,
    ⟨prime_16087, by decide, by decide⟩,
    ⟨prime_16091, by decide, by decide⟩,
    ⟨prime_16097, by decide, by decide⟩,
    ⟨prime_16103, by decide, by decide⟩,
    ⟨prime_16111, by decide, by decide⟩,
    ⟨prime_16127, by decide, by decide⟩,
    ⟨prime_16139, by decide, by decide⟩,
    ⟨prime_16141, by decide, by decide⟩,
    ⟨prime_16183, by decide, by decide⟩,
    ⟨prime_16187, by decide, by decide⟩,
    ⟨prime_16189, by decide, by decide⟩,
    ⟨prime_16193, by decide, by decide⟩,
    ⟨prime_16217, by decide, by decide⟩,
    ⟨prime_16223, by decide, by decide⟩,
    ⟨prime_16229, by decide, by decide⟩,
    ⟨prime_16231, by decide, by decide⟩,
    ⟨prime_16249, by decide, by decide⟩,
    ⟨prime_16253, by decide, by decide⟩,
    ⟨prime_16267, by decide, by decide⟩,
    ⟨prime_16273, by decide, by decide⟩,
    ⟨prime_16301, by decide, by decide⟩,
    ⟨prime_16319, by decide, by decide⟩,
    ⟨prime_16333, by decide, by decide⟩,
    ⟨prime_16339, by decide, by decide⟩,
    ⟨prime_16349, by decide, by decide⟩,
    ⟨prime_16361, by decide, by decide⟩,
    ⟨prime_16363, by decide, by decide⟩,
    ⟨prime_16369, by decide, by decide⟩,
    ⟨prime_16381, by decide, by decide⟩,
    ⟨prime_16411, by decide, by decide⟩,
    ⟨prime_16417, by decide, by decide⟩,
    ⟨prime_16421, by decide, by decide⟩,
    ⟨prime_16427, by decide, by decide⟩,
    ⟨prime_16433, by decide, by decide⟩,
    ⟨prime_16447, by decide, by decide⟩,
    ⟨prime_16451, by decide, by decide⟩,
    ⟨prime_16453, by decide, by decide⟩,
    ⟨prime_16477, by decide, by decide⟩,
    ⟨prime_16481, by decide, by decide⟩,
    ⟨prime_16487, by decide, by decide⟩,
    ⟨prime_16493, by decide, by decide⟩,
    ⟨prime_16519, by decide, by decide⟩,
    ⟨prime_16529, by decide, by decide⟩,
    ⟨prime_16547, by decide, by decide⟩,
    ⟨prime_16553, by decide, by decide⟩,
    ⟨prime_16561, by decide, by decide⟩,
    ⟨prime_16567, by decide, by decide⟩,
    ⟨prime_16573, by decide, by decide⟩,
    ⟨prime_16603, by decide, by decide⟩,
    ⟨prime_16607, by decide, by decide⟩
  ⟩

end B029
end Sude.Lucas.Generated
