import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0074
import Sude.GeneratedFTT.N0102
import Sude.GeneratedFTT.N0103
import Sude.GeneratedFTT.N0112
import Sude.GeneratedFTT.N0120
import Sude.GeneratedFTT.N0126
import Sude.GeneratedTwinBase.B008

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B010
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_4783, by decide, by decide⟩,
    ⟨prime_4787, by decide, by decide⟩,
    ⟨prime_4789, by decide, by decide⟩,
    ⟨prime_4793, by decide, by decide⟩,
    ⟨prime_4799, by decide, by decide⟩,
    ⟨prime_4801, by decide, by decide⟩,
    ⟨prime_4813, by decide, by decide⟩,
    ⟨prime_4817, by decide, by decide⟩,
    ⟨prime_4831, by decide, by decide⟩,
    ⟨prime_4861, by decide, by decide⟩,
    ⟨prime_4871, by decide, by decide⟩,
    ⟨prime_4877, by decide, by decide⟩,
    ⟨prime_4889, by decide, by decide⟩,
    ⟨prime_4903, by decide, by decide⟩,
    ⟨prime_4909, by decide, by decide⟩,
    ⟨prime_4919, by decide, by decide⟩,
    ⟨prime_4931, by decide, by decide⟩,
    ⟨prime_4933, by decide, by decide⟩,
    ⟨prime_4937, by decide, by decide⟩,
    ⟨prime_4943, by decide, by decide⟩,
    ⟨prime_4951, by decide, by decide⟩,
    ⟨prime_4957, by decide, by decide⟩,
    ⟨prime_4967, by decide, by decide⟩,
    ⟨prime_4969, by decide, by decide⟩,
    ⟨prime_4973, by decide, by decide⟩,
    ⟨prime_4987, by decide, by decide⟩,
    ⟨prime_4993, by decide, by decide⟩,
    ⟨prime_4999, by decide, by decide⟩,
    ⟨prime_5003, by decide, by decide⟩,
    ⟨prime_5009, by decide, by decide⟩,
    ⟨prime_5011, by decide, by decide⟩,
    ⟨prime_5021, by decide, by decide⟩,
    ⟨prime_5023, by decide, by decide⟩,
    ⟨prime_5039, by decide, by decide⟩,
    ⟨prime_5051, by decide, by decide⟩,
    ⟨prime_5059, by decide, by decide⟩,
    ⟨prime_5077, by decide, by decide⟩,
    ⟨prime_5081, by decide, by decide⟩,
    ⟨prime_5087, by decide, by decide⟩,
    ⟨prime_5099, by decide, by decide⟩,
    ⟨prime_5101, by decide, by decide⟩,
    ⟨prime_5107, by decide, by decide⟩,
    ⟨prime_5113, by decide, by decide⟩,
    ⟨prime_5119, by decide, by decide⟩,
    ⟨prime_5147, by decide, by decide⟩,
    ⟨prime_5153, by decide, by decide⟩,
    ⟨prime_5167, by decide, by decide⟩,
    ⟨prime_5171, by decide, by decide⟩,
    ⟨prime_5179, by decide, by decide⟩,
    ⟨prime_5189, by decide, by decide⟩,
    ⟨prime_5197, by decide, by decide⟩,
    ⟨prime_5209, by decide, by decide⟩,
    ⟨prime_5227, by decide, by decide⟩,
    ⟨prime_5231, by decide, by decide⟩,
    ⟨prime_5233, by decide, by decide⟩,
    ⟨prime_5237, by decide, by decide⟩,
    ⟨prime_5261, by decide, by decide⟩,
    ⟨prime_5273, by decide, by decide⟩,
    ⟨prime_5279, by decide, by decide⟩,
    ⟨prime_5281, by decide, by decide⟩,
    ⟨prime_5297, by decide, by decide⟩,
    ⟨prime_5303, by decide, by decide⟩,
    ⟨prime_5309, by decide, by decide⟩,
    ⟨prime_5323, by decide, by decide⟩
  ⟩

end B010
end Sude.Lucas.Generated
