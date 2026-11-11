import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0078
import Sude.GeneratedFTT.N0079
import Sude.GeneratedFTT.N0087
import Sude.GeneratedFTT.N0089
import Sude.GeneratedFTT.N0101
import Sude.GeneratedFTT.N0114
import Sude.GeneratedFTT.N0121
import Sude.GeneratedFTT.N0143
import Sude.GeneratedTwinBase.M000
import Sude.GeneratedTwinBase.B013

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B015
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993, 8009, 8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093, 8101, 8111, 8117, 8123, 8147, 8161, 8167]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_7577, by decide, by decide⟩,
    ⟨prime_7583, by decide, by decide⟩,
    ⟨prime_7589, by decide, by decide⟩,
    ⟨prime_7591, by decide, by decide⟩,
    ⟨prime_7603, by decide, by decide⟩,
    ⟨prime_7607, by decide, by decide⟩,
    ⟨prime_7621, by decide, by decide⟩,
    ⟨prime_7639, by decide, by decide⟩,
    ⟨prime_7643, by decide, by decide⟩,
    ⟨prime_7649, by decide, by decide⟩,
    ⟨prime_7669, by decide, by decide⟩,
    ⟨prime_7673, by decide, by decide⟩,
    ⟨prime_7681, by decide, by decide⟩,
    ⟨prime_7687, by decide, by decide⟩,
    ⟨prime_7691, by decide, by decide⟩,
    ⟨prime_7699, by decide, by decide⟩,
    ⟨prime_7703, by decide, by decide⟩,
    ⟨prime_7717, by decide, by decide⟩,
    ⟨prime_7723, by decide, by decide⟩,
    ⟨prime_7727, by decide, by decide⟩,
    ⟨prime_7741, by decide, by decide⟩,
    ⟨prime_7753, by decide, by decide⟩,
    ⟨prime_7757, by decide, by decide⟩,
    ⟨prime_7759, by decide, by decide⟩,
    ⟨prime_7789, by decide, by decide⟩,
    ⟨prime_7793, by decide, by decide⟩,
    ⟨prime_7817, by decide, by decide⟩,
    ⟨prime_7823, by decide, by decide⟩,
    ⟨prime_7829, by decide, by decide⟩,
    ⟨prime_7841, by decide, by decide⟩,
    ⟨prime_7853, by decide, by decide⟩,
    ⟨prime_7867, by decide, by decide⟩,
    ⟨prime_7873, by decide, by decide⟩,
    ⟨prime_7877, by decide, by decide⟩,
    ⟨prime_7879, by decide, by decide⟩,
    ⟨prime_7883, by decide, by decide⟩,
    ⟨prime_7901, by decide, by decide⟩,
    ⟨prime_7907, by decide, by decide⟩,
    ⟨prime_7919, by decide, by decide⟩,
    ⟨prime_7927, by decide, by decide⟩,
    ⟨prime_7933, by decide, by decide⟩,
    ⟨prime_7937, by decide, by decide⟩,
    ⟨prime_7949, by decide, by decide⟩,
    ⟨prime_7951, by decide, by decide⟩,
    ⟨prime_7963, by decide, by decide⟩,
    ⟨prime_7993, by decide, by decide⟩,
    ⟨prime_8009, by decide, by decide⟩,
    ⟨prime_8011, by decide, by decide⟩,
    ⟨prime_8017, by decide, by decide⟩,
    ⟨prime_8039, by decide, by decide⟩,
    ⟨prime_8053, by decide, by decide⟩,
    ⟨prime_8059, by decide, by decide⟩,
    ⟨prime_8069, by decide, by decide⟩,
    ⟨prime_8081, by decide, by decide⟩,
    ⟨prime_8087, by decide, by decide⟩,
    ⟨prime_8089, by decide, by decide⟩,
    ⟨prime_8093, by decide, by decide⟩,
    ⟨prime_8101, by decide, by decide⟩,
    ⟨prime_8111, by decide, by decide⟩,
    ⟨prime_8117, by decide, by decide⟩,
    ⟨prime_8123, by decide, by decide⟩,
    ⟨prime_8147, by decide, by decide⟩,
    ⟨prime_8161, by decide, by decide⟩,
    ⟨prime_8167, by decide, by decide⟩
  ⟩

end B015
end Sude.Lucas.Generated
