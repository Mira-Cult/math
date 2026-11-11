import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0064
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0088
import Sude.GeneratedFTT.N0092
import Sude.GeneratedFTT.N0093
import Sude.GeneratedFTT.N0094
import Sude.GeneratedFTT.N0107
import Sude.GeneratedFTT.N0111
import Sude.GeneratedFTT.N0122
import Sude.GeneratedFTT.N0124
import Sude.GeneratedFTT.N0127
import Sude.GeneratedFTT.N0130
import Sude.GeneratedFTT.N0137
import Sude.GeneratedFTT.N0139
import Sude.GeneratedFTT.N0142
import Sude.GeneratedTwinBase.M001
import Sude.GeneratedTwinBase.M002
import Sude.GeneratedTwinBase.B039

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B041
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [23603, 23609, 23623, 23627, 23629, 23633, 23663, 23669, 23671, 23677, 23687, 23689, 23719, 23741, 23743, 23747, 23753, 23761, 23767, 23773, 23789, 23801, 23813, 23819, 23827, 23831, 23833, 23857, 23869, 23873, 23879, 23887, 23893, 23899, 23909, 23911, 23917, 23929, 23957, 23971, 23977, 23981, 23993, 24001, 24007, 24019, 24023, 24029, 24043, 24049, 24061, 24071, 24077, 24083, 24091, 24097, 24103, 24107, 24109, 24113, 24121, 24133, 24137, 24151]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_23603, by decide, by decide⟩,
    ⟨prime_23609, by decide, by decide⟩,
    ⟨prime_23623, by decide, by decide⟩,
    ⟨prime_23627, by decide, by decide⟩,
    ⟨prime_23629, by decide, by decide⟩,
    ⟨prime_23633, by decide, by decide⟩,
    ⟨prime_23663, by decide, by decide⟩,
    ⟨prime_23669, by decide, by decide⟩,
    ⟨prime_23671, by decide, by decide⟩,
    ⟨prime_23677, by decide, by decide⟩,
    ⟨prime_23687, by decide, by decide⟩,
    ⟨prime_23689, by decide, by decide⟩,
    ⟨prime_23719, by decide, by decide⟩,
    ⟨prime_23741, by decide, by decide⟩,
    ⟨prime_23743, by decide, by decide⟩,
    ⟨prime_23747, by decide, by decide⟩,
    ⟨prime_23753, by decide, by decide⟩,
    ⟨prime_23761, by decide, by decide⟩,
    ⟨prime_23767, by decide, by decide⟩,
    ⟨prime_23773, by decide, by decide⟩,
    ⟨prime_23789, by decide, by decide⟩,
    ⟨prime_23801, by decide, by decide⟩,
    ⟨prime_23813, by decide, by decide⟩,
    ⟨prime_23819, by decide, by decide⟩,
    ⟨prime_23827, by decide, by decide⟩,
    ⟨prime_23831, by decide, by decide⟩,
    ⟨prime_23833, by decide, by decide⟩,
    ⟨prime_23857, by decide, by decide⟩,
    ⟨prime_23869, by decide, by decide⟩,
    ⟨prime_23873, by decide, by decide⟩,
    ⟨prime_23879, by decide, by decide⟩,
    ⟨prime_23887, by decide, by decide⟩,
    ⟨prime_23893, by decide, by decide⟩,
    ⟨prime_23899, by decide, by decide⟩,
    ⟨prime_23909, by decide, by decide⟩,
    ⟨prime_23911, by decide, by decide⟩,
    ⟨prime_23917, by decide, by decide⟩,
    ⟨prime_23929, by decide, by decide⟩,
    ⟨prime_23957, by decide, by decide⟩,
    ⟨prime_23971, by decide, by decide⟩,
    ⟨prime_23977, by decide, by decide⟩,
    ⟨prime_23981, by decide, by decide⟩,
    ⟨prime_23993, by decide, by decide⟩,
    ⟨prime_24001, by decide, by decide⟩,
    ⟨prime_24007, by decide, by decide⟩,
    ⟨prime_24019, by decide, by decide⟩,
    ⟨prime_24023, by decide, by decide⟩,
    ⟨prime_24029, by decide, by decide⟩,
    ⟨prime_24043, by decide, by decide⟩,
    ⟨prime_24049, by decide, by decide⟩,
    ⟨prime_24061, by decide, by decide⟩,
    ⟨prime_24071, by decide, by decide⟩,
    ⟨prime_24077, by decide, by decide⟩,
    ⟨prime_24083, by decide, by decide⟩,
    ⟨prime_24091, by decide, by decide⟩,
    ⟨prime_24097, by decide, by decide⟩,
    ⟨prime_24103, by decide, by decide⟩,
    ⟨prime_24107, by decide, by decide⟩,
    ⟨prime_24109, by decide, by decide⟩,
    ⟨prime_24113, by decide, by decide⟩,
    ⟨prime_24121, by decide, by decide⟩,
    ⟨prime_24133, by decide, by decide⟩,
    ⟨prime_24137, by decide, by decide⟩,
    ⟨prime_24151, by decide, by decide⟩
  ⟩

end B041
end Sude.Lucas.Generated
