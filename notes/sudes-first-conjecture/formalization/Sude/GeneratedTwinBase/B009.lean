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
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0081
import Sude.GeneratedFTT.N0099
import Sude.GeneratedTwinBase.B007

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B009
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_4219, by decide, by decide⟩,
    ⟨prime_4229, by decide, by decide⟩,
    ⟨prime_4231, by decide, by decide⟩,
    ⟨prime_4241, by decide, by decide⟩,
    ⟨prime_4243, by decide, by decide⟩,
    ⟨prime_4253, by decide, by decide⟩,
    ⟨prime_4259, by decide, by decide⟩,
    ⟨prime_4261, by decide, by decide⟩,
    ⟨prime_4271, by decide, by decide⟩,
    ⟨prime_4273, by decide, by decide⟩,
    ⟨prime_4283, by decide, by decide⟩,
    ⟨prime_4289, by decide, by decide⟩,
    ⟨prime_4297, by decide, by decide⟩,
    ⟨prime_4327, by decide, by decide⟩,
    ⟨prime_4337, by decide, by decide⟩,
    ⟨prime_4339, by decide, by decide⟩,
    ⟨prime_4349, by decide, by decide⟩,
    ⟨prime_4357, by decide, by decide⟩,
    ⟨prime_4363, by decide, by decide⟩,
    ⟨prime_4373, by decide, by decide⟩,
    ⟨prime_4391, by decide, by decide⟩,
    ⟨prime_4397, by decide, by decide⟩,
    ⟨prime_4409, by decide, by decide⟩,
    ⟨prime_4421, by decide, by decide⟩,
    ⟨prime_4423, by decide, by decide⟩,
    ⟨prime_4441, by decide, by decide⟩,
    ⟨prime_4447, by decide, by decide⟩,
    ⟨prime_4451, by decide, by decide⟩,
    ⟨prime_4457, by decide, by decide⟩,
    ⟨prime_4463, by decide, by decide⟩,
    ⟨prime_4481, by decide, by decide⟩,
    ⟨prime_4483, by decide, by decide⟩,
    ⟨prime_4493, by decide, by decide⟩,
    ⟨prime_4507, by decide, by decide⟩,
    ⟨prime_4513, by decide, by decide⟩,
    ⟨prime_4517, by decide, by decide⟩,
    ⟨prime_4519, by decide, by decide⟩,
    ⟨prime_4523, by decide, by decide⟩,
    ⟨prime_4547, by decide, by decide⟩,
    ⟨prime_4549, by decide, by decide⟩,
    ⟨prime_4561, by decide, by decide⟩,
    ⟨prime_4567, by decide, by decide⟩,
    ⟨prime_4583, by decide, by decide⟩,
    ⟨prime_4591, by decide, by decide⟩,
    ⟨prime_4597, by decide, by decide⟩,
    ⟨prime_4603, by decide, by decide⟩,
    ⟨prime_4621, by decide, by decide⟩,
    ⟨prime_4637, by decide, by decide⟩,
    ⟨prime_4639, by decide, by decide⟩,
    ⟨prime_4643, by decide, by decide⟩,
    ⟨prime_4649, by decide, by decide⟩,
    ⟨prime_4651, by decide, by decide⟩,
    ⟨prime_4657, by decide, by decide⟩,
    ⟨prime_4663, by decide, by decide⟩,
    ⟨prime_4673, by decide, by decide⟩,
    ⟨prime_4679, by decide, by decide⟩,
    ⟨prime_4691, by decide, by decide⟩,
    ⟨prime_4703, by decide, by decide⟩,
    ⟨prime_4721, by decide, by decide⟩,
    ⟨prime_4723, by decide, by decide⟩,
    ⟨prime_4729, by decide, by decide⟩,
    ⟨prime_4733, by decide, by decide⟩,
    ⟨prime_4751, by decide, by decide⟩,
    ⟨prime_4759, by decide, by decide⟩
  ⟩

end B009
end Sude.Lucas.Generated
