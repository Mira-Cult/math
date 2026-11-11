import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0053
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0075
import Sude.GeneratedFTT.N0081
import Sude.GeneratedFTT.N0086
import Sude.GeneratedFTT.N0087
import Sude.GeneratedFTT.N0095
import Sude.GeneratedFTT.N0100
import Sude.GeneratedFTT.N0104
import Sude.GeneratedFTT.N0106
import Sude.GeneratedFTT.N0112
import Sude.GeneratedFTT.N0113
import Sude.GeneratedFTT.N0116
import Sude.GeneratedFTT.N0117
import Sude.GeneratedFTT.N0122
import Sude.GeneratedFTT.N0148
import Sude.GeneratedTwinBase.M002
import Sude.GeneratedTwinBase.B040

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B042
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [24169, 24179, 24181, 24197, 24203, 24223, 24229, 24239, 24247, 24251, 24281, 24317, 24329, 24337, 24359, 24371, 24373, 24379, 24391, 24407, 24413, 24419, 24421, 24439, 24443, 24469, 24473, 24481, 24499, 24509, 24517, 24527, 24533, 24547, 24551, 24571, 24593, 24611, 24623, 24631, 24659, 24671, 24677, 24683, 24691, 24697, 24709, 24733, 24749, 24763, 24767, 24781, 24793, 24799, 24809, 24821, 24841, 24847, 24851, 24859, 24877, 24889, 24907, 24917]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_24169, by decide, by decide⟩,
    ⟨prime_24179, by decide, by decide⟩,
    ⟨prime_24181, by decide, by decide⟩,
    ⟨prime_24197, by decide, by decide⟩,
    ⟨prime_24203, by decide, by decide⟩,
    ⟨prime_24223, by decide, by decide⟩,
    ⟨prime_24229, by decide, by decide⟩,
    ⟨prime_24239, by decide, by decide⟩,
    ⟨prime_24247, by decide, by decide⟩,
    ⟨prime_24251, by decide, by decide⟩,
    ⟨prime_24281, by decide, by decide⟩,
    ⟨prime_24317, by decide, by decide⟩,
    ⟨prime_24329, by decide, by decide⟩,
    ⟨prime_24337, by decide, by decide⟩,
    ⟨prime_24359, by decide, by decide⟩,
    ⟨prime_24371, by decide, by decide⟩,
    ⟨prime_24373, by decide, by decide⟩,
    ⟨prime_24379, by decide, by decide⟩,
    ⟨prime_24391, by decide, by decide⟩,
    ⟨prime_24407, by decide, by decide⟩,
    ⟨prime_24413, by decide, by decide⟩,
    ⟨prime_24419, by decide, by decide⟩,
    ⟨prime_24421, by decide, by decide⟩,
    ⟨prime_24439, by decide, by decide⟩,
    ⟨prime_24443, by decide, by decide⟩,
    ⟨prime_24469, by decide, by decide⟩,
    ⟨prime_24473, by decide, by decide⟩,
    ⟨prime_24481, by decide, by decide⟩,
    ⟨prime_24499, by decide, by decide⟩,
    ⟨prime_24509, by decide, by decide⟩,
    ⟨prime_24517, by decide, by decide⟩,
    ⟨prime_24527, by decide, by decide⟩,
    ⟨prime_24533, by decide, by decide⟩,
    ⟨prime_24547, by decide, by decide⟩,
    ⟨prime_24551, by decide, by decide⟩,
    ⟨prime_24571, by decide, by decide⟩,
    ⟨prime_24593, by decide, by decide⟩,
    ⟨prime_24611, by decide, by decide⟩,
    ⟨prime_24623, by decide, by decide⟩,
    ⟨prime_24631, by decide, by decide⟩,
    ⟨prime_24659, by decide, by decide⟩,
    ⟨prime_24671, by decide, by decide⟩,
    ⟨prime_24677, by decide, by decide⟩,
    ⟨prime_24683, by decide, by decide⟩,
    ⟨prime_24691, by decide, by decide⟩,
    ⟨prime_24697, by decide, by decide⟩,
    ⟨prime_24709, by decide, by decide⟩,
    ⟨prime_24733, by decide, by decide⟩,
    ⟨prime_24749, by decide, by decide⟩,
    ⟨prime_24763, by decide, by decide⟩,
    ⟨prime_24767, by decide, by decide⟩,
    ⟨prime_24781, by decide, by decide⟩,
    ⟨prime_24793, by decide, by decide⟩,
    ⟨prime_24799, by decide, by decide⟩,
    ⟨prime_24809, by decide, by decide⟩,
    ⟨prime_24821, by decide, by decide⟩,
    ⟨prime_24841, by decide, by decide⟩,
    ⟨prime_24847, by decide, by decide⟩,
    ⟨prime_24851, by decide, by decide⟩,
    ⟨prime_24859, by decide, by decide⟩,
    ⟨prime_24877, by decide, by decide⟩,
    ⟨prime_24889, by decide, by decide⟩,
    ⟨prime_24907, by decide, by decide⟩,
    ⟨prime_24917, by decide, by decide⟩
  ⟩

end B042
end Sude.Lucas.Generated
