import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0085
import Sude.GeneratedTwinBase.B005

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B007
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_3181, by decide, by decide⟩,
    ⟨prime_3187, by decide, by decide⟩,
    ⟨prime_3191, by decide, by decide⟩,
    ⟨prime_3203, by decide, by decide⟩,
    ⟨prime_3209, by decide, by decide⟩,
    ⟨prime_3217, by decide, by decide⟩,
    ⟨prime_3221, by decide, by decide⟩,
    ⟨prime_3229, by decide, by decide⟩,
    ⟨prime_3251, by decide, by decide⟩,
    ⟨prime_3253, by decide, by decide⟩,
    ⟨prime_3257, by decide, by decide⟩,
    ⟨prime_3259, by decide, by decide⟩,
    ⟨prime_3271, by decide, by decide⟩,
    ⟨prime_3299, by decide, by decide⟩,
    ⟨prime_3301, by decide, by decide⟩,
    ⟨prime_3307, by decide, by decide⟩,
    ⟨prime_3313, by decide, by decide⟩,
    ⟨prime_3319, by decide, by decide⟩,
    ⟨prime_3323, by decide, by decide⟩,
    ⟨prime_3329, by decide, by decide⟩,
    ⟨prime_3331, by decide, by decide⟩,
    ⟨prime_3343, by decide, by decide⟩,
    ⟨prime_3347, by decide, by decide⟩,
    ⟨prime_3359, by decide, by decide⟩,
    ⟨prime_3361, by decide, by decide⟩,
    ⟨prime_3371, by decide, by decide⟩,
    ⟨prime_3373, by decide, by decide⟩,
    ⟨prime_3389, by decide, by decide⟩,
    ⟨prime_3391, by decide, by decide⟩,
    ⟨prime_3407, by decide, by decide⟩,
    ⟨prime_3413, by decide, by decide⟩,
    ⟨prime_3433, by decide, by decide⟩,
    ⟨prime_3449, by decide, by decide⟩,
    ⟨prime_3457, by decide, by decide⟩,
    ⟨prime_3461, by decide, by decide⟩,
    ⟨prime_3463, by decide, by decide⟩,
    ⟨prime_3467, by decide, by decide⟩,
    ⟨prime_3469, by decide, by decide⟩,
    ⟨prime_3491, by decide, by decide⟩,
    ⟨prime_3499, by decide, by decide⟩,
    ⟨prime_3511, by decide, by decide⟩,
    ⟨prime_3517, by decide, by decide⟩,
    ⟨prime_3527, by decide, by decide⟩,
    ⟨prime_3529, by decide, by decide⟩,
    ⟨prime_3533, by decide, by decide⟩,
    ⟨prime_3539, by decide, by decide⟩,
    ⟨prime_3541, by decide, by decide⟩,
    ⟨prime_3547, by decide, by decide⟩,
    ⟨prime_3557, by decide, by decide⟩,
    ⟨prime_3559, by decide, by decide⟩,
    ⟨prime_3571, by decide, by decide⟩,
    ⟨prime_3581, by decide, by decide⟩,
    ⟨prime_3583, by decide, by decide⟩,
    ⟨prime_3593, by decide, by decide⟩,
    ⟨prime_3607, by decide, by decide⟩,
    ⟨prime_3613, by decide, by decide⟩,
    ⟨prime_3617, by decide, by decide⟩,
    ⟨prime_3623, by decide, by decide⟩,
    ⟨prime_3631, by decide, by decide⟩,
    ⟨prime_3637, by decide, by decide⟩,
    ⟨prime_3643, by decide, by decide⟩,
    ⟨prime_3659, by decide, by decide⟩,
    ⟨prime_3671, by decide, by decide⟩,
    ⟨prime_3673, by decide, by decide⟩
  ⟩

end B007
end Sude.Lucas.Generated
