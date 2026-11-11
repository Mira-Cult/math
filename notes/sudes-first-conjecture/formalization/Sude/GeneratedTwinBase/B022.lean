import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0083
import Sude.GeneratedFTT.N0086
import Sude.GeneratedFTT.N0087
import Sude.GeneratedFTT.N0091
import Sude.GeneratedFTT.N0094
import Sude.GeneratedFTT.N0095
import Sude.GeneratedFTT.N0096
import Sude.GeneratedFTT.N0097
import Sude.GeneratedFTT.N0103
import Sude.GeneratedFTT.N0109
import Sude.GeneratedFTT.N0118
import Sude.GeneratedFTT.N0124
import Sude.GeneratedFTT.N0126
import Sude.GeneratedFTT.N0129
import Sude.GeneratedFTT.N0138
import Sude.GeneratedFTT.N0139
import Sude.GeneratedTwinBase.M000
import Sude.GeneratedTwinBase.B020

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B022
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [11777, 11779, 11783, 11789, 11801, 11807, 11813, 11821, 11827, 11831, 11833, 11839, 11863, 11867, 11887, 11897, 11903, 11909, 11923, 11927, 11933, 11939, 11941, 11953, 11959, 11969, 11971, 11981, 11987, 12007, 12011, 12037, 12041, 12043, 12049, 12071, 12073, 12097, 12101, 12107, 12109, 12113, 12119, 12143, 12149, 12157, 12161, 12163, 12197, 12203, 12211, 12227, 12239, 12241, 12251, 12253, 12263, 12269, 12277, 12281, 12289, 12301, 12323, 12329]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_11777, by decide, by decide⟩,
    ⟨prime_11779, by decide, by decide⟩,
    ⟨prime_11783, by decide, by decide⟩,
    ⟨prime_11789, by decide, by decide⟩,
    ⟨prime_11801, by decide, by decide⟩,
    ⟨prime_11807, by decide, by decide⟩,
    ⟨prime_11813, by decide, by decide⟩,
    ⟨prime_11821, by decide, by decide⟩,
    ⟨prime_11827, by decide, by decide⟩,
    ⟨prime_11831, by decide, by decide⟩,
    ⟨prime_11833, by decide, by decide⟩,
    ⟨prime_11839, by decide, by decide⟩,
    ⟨prime_11863, by decide, by decide⟩,
    ⟨prime_11867, by decide, by decide⟩,
    ⟨prime_11887, by decide, by decide⟩,
    ⟨prime_11897, by decide, by decide⟩,
    ⟨prime_11903, by decide, by decide⟩,
    ⟨prime_11909, by decide, by decide⟩,
    ⟨prime_11923, by decide, by decide⟩,
    ⟨prime_11927, by decide, by decide⟩,
    ⟨prime_11933, by decide, by decide⟩,
    ⟨prime_11939, by decide, by decide⟩,
    ⟨prime_11941, by decide, by decide⟩,
    ⟨prime_11953, by decide, by decide⟩,
    ⟨prime_11959, by decide, by decide⟩,
    ⟨prime_11969, by decide, by decide⟩,
    ⟨prime_11971, by decide, by decide⟩,
    ⟨prime_11981, by decide, by decide⟩,
    ⟨prime_11987, by decide, by decide⟩,
    ⟨prime_12007, by decide, by decide⟩,
    ⟨prime_12011, by decide, by decide⟩,
    ⟨prime_12037, by decide, by decide⟩,
    ⟨prime_12041, by decide, by decide⟩,
    ⟨prime_12043, by decide, by decide⟩,
    ⟨prime_12049, by decide, by decide⟩,
    ⟨prime_12071, by decide, by decide⟩,
    ⟨prime_12073, by decide, by decide⟩,
    ⟨prime_12097, by decide, by decide⟩,
    ⟨prime_12101, by decide, by decide⟩,
    ⟨prime_12107, by decide, by decide⟩,
    ⟨prime_12109, by decide, by decide⟩,
    ⟨prime_12113, by decide, by decide⟩,
    ⟨prime_12119, by decide, by decide⟩,
    ⟨prime_12143, by decide, by decide⟩,
    ⟨prime_12149, by decide, by decide⟩,
    ⟨prime_12157, by decide, by decide⟩,
    ⟨prime_12161, by decide, by decide⟩,
    ⟨prime_12163, by decide, by decide⟩,
    ⟨prime_12197, by decide, by decide⟩,
    ⟨prime_12203, by decide, by decide⟩,
    ⟨prime_12211, by decide, by decide⟩,
    ⟨prime_12227, by decide, by decide⟩,
    ⟨prime_12239, by decide, by decide⟩,
    ⟨prime_12241, by decide, by decide⟩,
    ⟨prime_12251, by decide, by decide⟩,
    ⟨prime_12253, by decide, by decide⟩,
    ⟨prime_12263, by decide, by decide⟩,
    ⟨prime_12269, by decide, by decide⟩,
    ⟨prime_12277, by decide, by decide⟩,
    ⟨prime_12281, by decide, by decide⟩,
    ⟨prime_12289, by decide, by decide⟩,
    ⟨prime_12301, by decide, by decide⟩,
    ⟨prime_12323, by decide, by decide⟩,
    ⟨prime_12329, by decide, by decide⟩
  ⟩

end B022
end Sude.Lucas.Generated
