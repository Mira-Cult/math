import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0053
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0064
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0074
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0082
import Sude.GeneratedFTT.N0108
import Sude.GeneratedFTT.N0109
import Sude.GeneratedFTT.N0117
import Sude.GeneratedFTT.N0119
import Sude.GeneratedFTT.N0124
import Sude.GeneratedFTT.N0135
import Sude.GeneratedFTT.N0136
import Sude.GeneratedFTT.N0141
import Sude.GeneratedFTT.N0146
import Sude.GeneratedFTT.N0148
import Sude.GeneratedTwinBase.M000
import Sude.GeneratedTwinBase.B023

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B025
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [13523, 13537, 13553, 13567, 13577, 13591, 13597, 13613, 13619, 13627, 13633, 13649, 13669, 13679, 13681, 13687, 13691, 13693, 13697, 13709, 13711, 13721, 13723, 13729, 13751, 13757, 13759, 13763, 13781, 13789, 13799, 13807, 13829, 13831, 13841, 13859, 13873, 13877, 13879, 13883, 13901, 13903, 13907, 13913, 13921, 13931, 13933, 13963, 13967, 13997, 13999, 14009, 14011, 14029, 14033, 14051, 14057, 14071, 14081, 14083, 14087, 14107, 14143, 14149]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_13523, by decide, by decide⟩,
    ⟨prime_13537, by decide, by decide⟩,
    ⟨prime_13553, by decide, by decide⟩,
    ⟨prime_13567, by decide, by decide⟩,
    ⟨prime_13577, by decide, by decide⟩,
    ⟨prime_13591, by decide, by decide⟩,
    ⟨prime_13597, by decide, by decide⟩,
    ⟨prime_13613, by decide, by decide⟩,
    ⟨prime_13619, by decide, by decide⟩,
    ⟨prime_13627, by decide, by decide⟩,
    ⟨prime_13633, by decide, by decide⟩,
    ⟨prime_13649, by decide, by decide⟩,
    ⟨prime_13669, by decide, by decide⟩,
    ⟨prime_13679, by decide, by decide⟩,
    ⟨prime_13681, by decide, by decide⟩,
    ⟨prime_13687, by decide, by decide⟩,
    ⟨prime_13691, by decide, by decide⟩,
    ⟨prime_13693, by decide, by decide⟩,
    ⟨prime_13697, by decide, by decide⟩,
    ⟨prime_13709, by decide, by decide⟩,
    ⟨prime_13711, by decide, by decide⟩,
    ⟨prime_13721, by decide, by decide⟩,
    ⟨prime_13723, by decide, by decide⟩,
    ⟨prime_13729, by decide, by decide⟩,
    ⟨prime_13751, by decide, by decide⟩,
    ⟨prime_13757, by decide, by decide⟩,
    ⟨prime_13759, by decide, by decide⟩,
    ⟨prime_13763, by decide, by decide⟩,
    ⟨prime_13781, by decide, by decide⟩,
    ⟨prime_13789, by decide, by decide⟩,
    ⟨prime_13799, by decide, by decide⟩,
    ⟨prime_13807, by decide, by decide⟩,
    ⟨prime_13829, by decide, by decide⟩,
    ⟨prime_13831, by decide, by decide⟩,
    ⟨prime_13841, by decide, by decide⟩,
    ⟨prime_13859, by decide, by decide⟩,
    ⟨prime_13873, by decide, by decide⟩,
    ⟨prime_13877, by decide, by decide⟩,
    ⟨prime_13879, by decide, by decide⟩,
    ⟨prime_13883, by decide, by decide⟩,
    ⟨prime_13901, by decide, by decide⟩,
    ⟨prime_13903, by decide, by decide⟩,
    ⟨prime_13907, by decide, by decide⟩,
    ⟨prime_13913, by decide, by decide⟩,
    ⟨prime_13921, by decide, by decide⟩,
    ⟨prime_13931, by decide, by decide⟩,
    ⟨prime_13933, by decide, by decide⟩,
    ⟨prime_13963, by decide, by decide⟩,
    ⟨prime_13967, by decide, by decide⟩,
    ⟨prime_13997, by decide, by decide⟩,
    ⟨prime_13999, by decide, by decide⟩,
    ⟨prime_14009, by decide, by decide⟩,
    ⟨prime_14011, by decide, by decide⟩,
    ⟨prime_14029, by decide, by decide⟩,
    ⟨prime_14033, by decide, by decide⟩,
    ⟨prime_14051, by decide, by decide⟩,
    ⟨prime_14057, by decide, by decide⟩,
    ⟨prime_14071, by decide, by decide⟩,
    ⟨prime_14081, by decide, by decide⟩,
    ⟨prime_14083, by decide, by decide⟩,
    ⟨prime_14087, by decide, by decide⟩,
    ⟨prime_14107, by decide, by decide⟩,
    ⟨prime_14143, by decide, by decide⟩,
    ⟨prime_14149, by decide, by decide⟩
  ⟩

end B025
end Sude.Lucas.Generated
