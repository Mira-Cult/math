import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0053
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0074
import Sude.GeneratedFTT.N0081
import Sude.GeneratedFTT.N0084
import Sude.GeneratedFTT.N0088
import Sude.GeneratedFTT.N0091
import Sude.GeneratedFTT.N0095
import Sude.GeneratedFTT.N0100
import Sude.GeneratedFTT.N0102
import Sude.GeneratedFTT.N0126
import Sude.GeneratedFTT.N0149
import Sude.GeneratedTwinBase.B010

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B012
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987, 6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143, 6151, 6163, 6173, 6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379, 6389]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_5857, by decide, by decide⟩,
    ⟨prime_5861, by decide, by decide⟩,
    ⟨prime_5867, by decide, by decide⟩,
    ⟨prime_5869, by decide, by decide⟩,
    ⟨prime_5879, by decide, by decide⟩,
    ⟨prime_5881, by decide, by decide⟩,
    ⟨prime_5897, by decide, by decide⟩,
    ⟨prime_5903, by decide, by decide⟩,
    ⟨prime_5923, by decide, by decide⟩,
    ⟨prime_5927, by decide, by decide⟩,
    ⟨prime_5939, by decide, by decide⟩,
    ⟨prime_5953, by decide, by decide⟩,
    ⟨prime_5981, by decide, by decide⟩,
    ⟨prime_5987, by decide, by decide⟩,
    ⟨prime_6007, by decide, by decide⟩,
    ⟨prime_6011, by decide, by decide⟩,
    ⟨prime_6029, by decide, by decide⟩,
    ⟨prime_6037, by decide, by decide⟩,
    ⟨prime_6043, by decide, by decide⟩,
    ⟨prime_6047, by decide, by decide⟩,
    ⟨prime_6053, by decide, by decide⟩,
    ⟨prime_6067, by decide, by decide⟩,
    ⟨prime_6073, by decide, by decide⟩,
    ⟨prime_6079, by decide, by decide⟩,
    ⟨prime_6089, by decide, by decide⟩,
    ⟨prime_6091, by decide, by decide⟩,
    ⟨prime_6101, by decide, by decide⟩,
    ⟨prime_6113, by decide, by decide⟩,
    ⟨prime_6121, by decide, by decide⟩,
    ⟨prime_6131, by decide, by decide⟩,
    ⟨prime_6133, by decide, by decide⟩,
    ⟨prime_6143, by decide, by decide⟩,
    ⟨prime_6151, by decide, by decide⟩,
    ⟨prime_6163, by decide, by decide⟩,
    ⟨prime_6173, by decide, by decide⟩,
    ⟨prime_6197, by decide, by decide⟩,
    ⟨prime_6199, by decide, by decide⟩,
    ⟨prime_6203, by decide, by decide⟩,
    ⟨prime_6211, by decide, by decide⟩,
    ⟨prime_6217, by decide, by decide⟩,
    ⟨prime_6221, by decide, by decide⟩,
    ⟨prime_6229, by decide, by decide⟩,
    ⟨prime_6247, by decide, by decide⟩,
    ⟨prime_6257, by decide, by decide⟩,
    ⟨prime_6263, by decide, by decide⟩,
    ⟨prime_6269, by decide, by decide⟩,
    ⟨prime_6271, by decide, by decide⟩,
    ⟨prime_6277, by decide, by decide⟩,
    ⟨prime_6287, by decide, by decide⟩,
    ⟨prime_6299, by decide, by decide⟩,
    ⟨prime_6301, by decide, by decide⟩,
    ⟨prime_6311, by decide, by decide⟩,
    ⟨prime_6317, by decide, by decide⟩,
    ⟨prime_6323, by decide, by decide⟩,
    ⟨prime_6329, by decide, by decide⟩,
    ⟨prime_6337, by decide, by decide⟩,
    ⟨prime_6343, by decide, by decide⟩,
    ⟨prime_6353, by decide, by decide⟩,
    ⟨prime_6359, by decide, by decide⟩,
    ⟨prime_6361, by decide, by decide⟩,
    ⟨prime_6367, by decide, by decide⟩,
    ⟨prime_6373, by decide, by decide⟩,
    ⟨prime_6379, by decide, by decide⟩,
    ⟨prime_6389, by decide, by decide⟩
  ⟩

end B012
end Sude.Lucas.Generated
