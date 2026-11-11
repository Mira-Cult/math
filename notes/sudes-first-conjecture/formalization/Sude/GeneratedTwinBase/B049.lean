import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0075
import Sude.GeneratedFTT.N0097
import Sude.GeneratedFTT.N0110
import Sude.GeneratedFTT.N0112
import Sude.GeneratedFTT.N0117
import Sude.GeneratedFTT.N0122
import Sude.GeneratedFTT.N0126
import Sude.GeneratedFTT.N0135
import Sude.GeneratedFTT.N0141
import Sude.GeneratedFTT.N0144
import Sude.GeneratedTwinBase.M003
import Sude.GeneratedTwinBase.B047

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B049
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [28813, 28817, 28837, 28843, 28859, 28867, 28871, 28879, 28901, 28909, 28921, 28927, 28933, 28949, 28961, 28979, 29009, 29017, 29021, 29023, 29027, 29033, 29059, 29063, 29077, 29101, 29123, 29129, 29131, 29137, 29147, 29153, 29167, 29173, 29179, 29191, 29201, 29207, 29209, 29221, 29231, 29243, 29251, 29269, 29287, 29297, 29303, 29311, 29327, 29333, 29339, 29347, 29363, 29383, 29387, 29389, 29399, 29401, 29411, 29423, 29429, 29437, 29443, 29453]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_28813, by decide, by decide⟩,
    ⟨prime_28817, by decide, by decide⟩,
    ⟨prime_28837, by decide, by decide⟩,
    ⟨prime_28843, by decide, by decide⟩,
    ⟨prime_28859, by decide, by decide⟩,
    ⟨prime_28867, by decide, by decide⟩,
    ⟨prime_28871, by decide, by decide⟩,
    ⟨prime_28879, by decide, by decide⟩,
    ⟨prime_28901, by decide, by decide⟩,
    ⟨prime_28909, by decide, by decide⟩,
    ⟨prime_28921, by decide, by decide⟩,
    ⟨prime_28927, by decide, by decide⟩,
    ⟨prime_28933, by decide, by decide⟩,
    ⟨prime_28949, by decide, by decide⟩,
    ⟨prime_28961, by decide, by decide⟩,
    ⟨prime_28979, by decide, by decide⟩,
    ⟨prime_29009, by decide, by decide⟩,
    ⟨prime_29017, by decide, by decide⟩,
    ⟨prime_29021, by decide, by decide⟩,
    ⟨prime_29023, by decide, by decide⟩,
    ⟨prime_29027, by decide, by decide⟩,
    ⟨prime_29033, by decide, by decide⟩,
    ⟨prime_29059, by decide, by decide⟩,
    ⟨prime_29063, by decide, by decide⟩,
    ⟨prime_29077, by decide, by decide⟩,
    ⟨prime_29101, by decide, by decide⟩,
    ⟨prime_29123, by decide, by decide⟩,
    ⟨prime_29129, by decide, by decide⟩,
    ⟨prime_29131, by decide, by decide⟩,
    ⟨prime_29137, by decide, by decide⟩,
    ⟨prime_29147, by decide, by decide⟩,
    ⟨prime_29153, by decide, by decide⟩,
    ⟨prime_29167, by decide, by decide⟩,
    ⟨prime_29173, by decide, by decide⟩,
    ⟨prime_29179, by decide, by decide⟩,
    ⟨prime_29191, by decide, by decide⟩,
    ⟨prime_29201, by decide, by decide⟩,
    ⟨prime_29207, by decide, by decide⟩,
    ⟨prime_29209, by decide, by decide⟩,
    ⟨prime_29221, by decide, by decide⟩,
    ⟨prime_29231, by decide, by decide⟩,
    ⟨prime_29243, by decide, by decide⟩,
    ⟨prime_29251, by decide, by decide⟩,
    ⟨prime_29269, by decide, by decide⟩,
    ⟨prime_29287, by decide, by decide⟩,
    ⟨prime_29297, by decide, by decide⟩,
    ⟨prime_29303, by decide, by decide⟩,
    ⟨prime_29311, by decide, by decide⟩,
    ⟨prime_29327, by decide, by decide⟩,
    ⟨prime_29333, by decide, by decide⟩,
    ⟨prime_29339, by decide, by decide⟩,
    ⟨prime_29347, by decide, by decide⟩,
    ⟨prime_29363, by decide, by decide⟩,
    ⟨prime_29383, by decide, by decide⟩,
    ⟨prime_29387, by decide, by decide⟩,
    ⟨prime_29389, by decide, by decide⟩,
    ⟨prime_29399, by decide, by decide⟩,
    ⟨prime_29401, by decide, by decide⟩,
    ⟨prime_29411, by decide, by decide⟩,
    ⟨prime_29423, by decide, by decide⟩,
    ⟨prime_29429, by decide, by decide⟩,
    ⟨prime_29437, by decide, by decide⟩,
    ⟨prime_29443, by decide, by decide⟩,
    ⟨prime_29453, by decide, by decide⟩
  ⟩

end B049
end Sude.Lucas.Generated
