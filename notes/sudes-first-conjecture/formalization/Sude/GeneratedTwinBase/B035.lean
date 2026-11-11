import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0078
import Sude.GeneratedFTT.N0088
import Sude.GeneratedFTT.N0089
import Sude.GeneratedFTT.N0096
import Sude.GeneratedFTT.N0098
import Sude.GeneratedFTT.N0099
import Sude.GeneratedFTT.N0100
import Sude.GeneratedFTT.N0107
import Sude.GeneratedFTT.N0108
import Sude.GeneratedFTT.N0121
import Sude.GeneratedFTT.N0122
import Sude.GeneratedFTT.N0123
import Sude.GeneratedFTT.N0126
import Sude.GeneratedFTT.N0134
import Sude.GeneratedFTT.N0140
import Sude.GeneratedFTT.N0146
import Sude.GeneratedTwinBase.M001
import Sude.GeneratedTwinBase.B033

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B035
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [19813, 19819, 19841, 19843, 19853, 19861, 19867, 19889, 19891, 19913, 19919, 19927, 19937, 19949, 19961, 19963, 19973, 19979, 19991, 19993, 19997, 20011, 20021, 20023, 20029, 20047, 20051, 20063, 20071, 20089, 20101, 20107, 20113, 20117, 20123, 20129, 20143, 20147, 20149, 20161, 20173, 20177, 20183, 20201, 20219, 20231, 20233, 20249, 20261, 20269, 20287, 20297, 20323, 20327, 20333, 20341, 20347, 20353, 20357, 20359, 20369, 20389, 20393, 20399]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_19813, by decide, by decide⟩,
    ⟨prime_19819, by decide, by decide⟩,
    ⟨prime_19841, by decide, by decide⟩,
    ⟨prime_19843, by decide, by decide⟩,
    ⟨prime_19853, by decide, by decide⟩,
    ⟨prime_19861, by decide, by decide⟩,
    ⟨prime_19867, by decide, by decide⟩,
    ⟨prime_19889, by decide, by decide⟩,
    ⟨prime_19891, by decide, by decide⟩,
    ⟨prime_19913, by decide, by decide⟩,
    ⟨prime_19919, by decide, by decide⟩,
    ⟨prime_19927, by decide, by decide⟩,
    ⟨prime_19937, by decide, by decide⟩,
    ⟨prime_19949, by decide, by decide⟩,
    ⟨prime_19961, by decide, by decide⟩,
    ⟨prime_19963, by decide, by decide⟩,
    ⟨prime_19973, by decide, by decide⟩,
    ⟨prime_19979, by decide, by decide⟩,
    ⟨prime_19991, by decide, by decide⟩,
    ⟨prime_19993, by decide, by decide⟩,
    ⟨prime_19997, by decide, by decide⟩,
    ⟨prime_20011, by decide, by decide⟩,
    ⟨prime_20021, by decide, by decide⟩,
    ⟨prime_20023, by decide, by decide⟩,
    ⟨prime_20029, by decide, by decide⟩,
    ⟨prime_20047, by decide, by decide⟩,
    ⟨prime_20051, by decide, by decide⟩,
    ⟨prime_20063, by decide, by decide⟩,
    ⟨prime_20071, by decide, by decide⟩,
    ⟨prime_20089, by decide, by decide⟩,
    ⟨prime_20101, by decide, by decide⟩,
    ⟨prime_20107, by decide, by decide⟩,
    ⟨prime_20113, by decide, by decide⟩,
    ⟨prime_20117, by decide, by decide⟩,
    ⟨prime_20123, by decide, by decide⟩,
    ⟨prime_20129, by decide, by decide⟩,
    ⟨prime_20143, by decide, by decide⟩,
    ⟨prime_20147, by decide, by decide⟩,
    ⟨prime_20149, by decide, by decide⟩,
    ⟨prime_20161, by decide, by decide⟩,
    ⟨prime_20173, by decide, by decide⟩,
    ⟨prime_20177, by decide, by decide⟩,
    ⟨prime_20183, by decide, by decide⟩,
    ⟨prime_20201, by decide, by decide⟩,
    ⟨prime_20219, by decide, by decide⟩,
    ⟨prime_20231, by decide, by decide⟩,
    ⟨prime_20233, by decide, by decide⟩,
    ⟨prime_20249, by decide, by decide⟩,
    ⟨prime_20261, by decide, by decide⟩,
    ⟨prime_20269, by decide, by decide⟩,
    ⟨prime_20287, by decide, by decide⟩,
    ⟨prime_20297, by decide, by decide⟩,
    ⟨prime_20323, by decide, by decide⟩,
    ⟨prime_20327, by decide, by decide⟩,
    ⟨prime_20333, by decide, by decide⟩,
    ⟨prime_20341, by decide, by decide⟩,
    ⟨prime_20347, by decide, by decide⟩,
    ⟨prime_20353, by decide, by decide⟩,
    ⟨prime_20357, by decide, by decide⟩,
    ⟨prime_20359, by decide, by decide⟩,
    ⟨prime_20369, by decide, by decide⟩,
    ⟨prime_20389, by decide, by decide⟩,
    ⟨prime_20393, by decide, by decide⟩,
    ⟨prime_20399, by decide, by decide⟩
  ⟩

end B035
end Sude.Lucas.Generated
