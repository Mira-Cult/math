import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0053
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0074
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0080
import Sude.GeneratedFTT.N0091
import Sude.GeneratedFTT.N0094
import Sude.GeneratedFTT.N0095
import Sude.GeneratedFTT.N0097
import Sude.GeneratedFTT.N0101
import Sude.GeneratedFTT.N0103
import Sude.GeneratedFTT.N0105
import Sude.GeneratedFTT.N0106
import Sude.GeneratedFTT.N0110
import Sude.GeneratedFTT.N0116
import Sude.GeneratedFTT.N0144
import Sude.GeneratedTwinBase.M000
import Sude.GeneratedTwinBase.B022

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B024
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [12917, 12919, 12923, 12941, 12953, 12959, 12967, 12973, 12979, 12983, 13001, 13003, 13007, 13009, 13033, 13037, 13043, 13049, 13063, 13093, 13099, 13103, 13109, 13121, 13127, 13147, 13151, 13159, 13163, 13171, 13177, 13183, 13187, 13217, 13219, 13229, 13241, 13249, 13259, 13267, 13291, 13297, 13309, 13313, 13327, 13331, 13337, 13339, 13367, 13381, 13397, 13399, 13411, 13417, 13421, 13441, 13451, 13457, 13463, 13469, 13477, 13487, 13499, 13513]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_12917, by decide, by decide⟩,
    ⟨prime_12919, by decide, by decide⟩,
    ⟨prime_12923, by decide, by decide⟩,
    ⟨prime_12941, by decide, by decide⟩,
    ⟨prime_12953, by decide, by decide⟩,
    ⟨prime_12959, by decide, by decide⟩,
    ⟨prime_12967, by decide, by decide⟩,
    ⟨prime_12973, by decide, by decide⟩,
    ⟨prime_12979, by decide, by decide⟩,
    ⟨prime_12983, by decide, by decide⟩,
    ⟨prime_13001, by decide, by decide⟩,
    ⟨prime_13003, by decide, by decide⟩,
    ⟨prime_13007, by decide, by decide⟩,
    ⟨prime_13009, by decide, by decide⟩,
    ⟨prime_13033, by decide, by decide⟩,
    ⟨prime_13037, by decide, by decide⟩,
    ⟨prime_13043, by decide, by decide⟩,
    ⟨prime_13049, by decide, by decide⟩,
    ⟨prime_13063, by decide, by decide⟩,
    ⟨prime_13093, by decide, by decide⟩,
    ⟨prime_13099, by decide, by decide⟩,
    ⟨prime_13103, by decide, by decide⟩,
    ⟨prime_13109, by decide, by decide⟩,
    ⟨prime_13121, by decide, by decide⟩,
    ⟨prime_13127, by decide, by decide⟩,
    ⟨prime_13147, by decide, by decide⟩,
    ⟨prime_13151, by decide, by decide⟩,
    ⟨prime_13159, by decide, by decide⟩,
    ⟨prime_13163, by decide, by decide⟩,
    ⟨prime_13171, by decide, by decide⟩,
    ⟨prime_13177, by decide, by decide⟩,
    ⟨prime_13183, by decide, by decide⟩,
    ⟨prime_13187, by decide, by decide⟩,
    ⟨prime_13217, by decide, by decide⟩,
    ⟨prime_13219, by decide, by decide⟩,
    ⟨prime_13229, by decide, by decide⟩,
    ⟨prime_13241, by decide, by decide⟩,
    ⟨prime_13249, by decide, by decide⟩,
    ⟨prime_13259, by decide, by decide⟩,
    ⟨prime_13267, by decide, by decide⟩,
    ⟨prime_13291, by decide, by decide⟩,
    ⟨prime_13297, by decide, by decide⟩,
    ⟨prime_13309, by decide, by decide⟩,
    ⟨prime_13313, by decide, by decide⟩,
    ⟨prime_13327, by decide, by decide⟩,
    ⟨prime_13331, by decide, by decide⟩,
    ⟨prime_13337, by decide, by decide⟩,
    ⟨prime_13339, by decide, by decide⟩,
    ⟨prime_13367, by decide, by decide⟩,
    ⟨prime_13381, by decide, by decide⟩,
    ⟨prime_13397, by decide, by decide⟩,
    ⟨prime_13399, by decide, by decide⟩,
    ⟨prime_13411, by decide, by decide⟩,
    ⟨prime_13417, by decide, by decide⟩,
    ⟨prime_13421, by decide, by decide⟩,
    ⟨prime_13441, by decide, by decide⟩,
    ⟨prime_13451, by decide, by decide⟩,
    ⟨prime_13457, by decide, by decide⟩,
    ⟨prime_13463, by decide, by decide⟩,
    ⟨prime_13469, by decide, by decide⟩,
    ⟨prime_13477, by decide, by decide⟩,
    ⟨prime_13487, by decide, by decide⟩,
    ⟨prime_13499, by decide, by decide⟩,
    ⟨prime_13513, by decide, by decide⟩
  ⟩

end B024
end Sude.Lucas.Generated
