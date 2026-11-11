import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0115
import Sude.GeneratedTwinBase.B006

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B008
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_3677, by decide, by decide⟩,
    ⟨prime_3691, by decide, by decide⟩,
    ⟨prime_3697, by decide, by decide⟩,
    ⟨prime_3701, by decide, by decide⟩,
    ⟨prime_3709, by decide, by decide⟩,
    ⟨prime_3719, by decide, by decide⟩,
    ⟨prime_3727, by decide, by decide⟩,
    ⟨prime_3733, by decide, by decide⟩,
    ⟨prime_3739, by decide, by decide⟩,
    ⟨prime_3761, by decide, by decide⟩,
    ⟨prime_3767, by decide, by decide⟩,
    ⟨prime_3769, by decide, by decide⟩,
    ⟨prime_3779, by decide, by decide⟩,
    ⟨prime_3793, by decide, by decide⟩,
    ⟨prime_3797, by decide, by decide⟩,
    ⟨prime_3803, by decide, by decide⟩,
    ⟨prime_3821, by decide, by decide⟩,
    ⟨prime_3823, by decide, by decide⟩,
    ⟨prime_3833, by decide, by decide⟩,
    ⟨prime_3847, by decide, by decide⟩,
    ⟨prime_3851, by decide, by decide⟩,
    ⟨prime_3853, by decide, by decide⟩,
    ⟨prime_3863, by decide, by decide⟩,
    ⟨prime_3877, by decide, by decide⟩,
    ⟨prime_3881, by decide, by decide⟩,
    ⟨prime_3889, by decide, by decide⟩,
    ⟨prime_3907, by decide, by decide⟩,
    ⟨prime_3911, by decide, by decide⟩,
    ⟨prime_3917, by decide, by decide⟩,
    ⟨prime_3919, by decide, by decide⟩,
    ⟨prime_3923, by decide, by decide⟩,
    ⟨prime_3929, by decide, by decide⟩,
    ⟨prime_3931, by decide, by decide⟩,
    ⟨prime_3943, by decide, by decide⟩,
    ⟨prime_3947, by decide, by decide⟩,
    ⟨prime_3967, by decide, by decide⟩,
    ⟨prime_3989, by decide, by decide⟩,
    ⟨prime_4001, by decide, by decide⟩,
    ⟨prime_4003, by decide, by decide⟩,
    ⟨prime_4007, by decide, by decide⟩,
    ⟨prime_4013, by decide, by decide⟩,
    ⟨prime_4019, by decide, by decide⟩,
    ⟨prime_4021, by decide, by decide⟩,
    ⟨prime_4027, by decide, by decide⟩,
    ⟨prime_4049, by decide, by decide⟩,
    ⟨prime_4051, by decide, by decide⟩,
    ⟨prime_4057, by decide, by decide⟩,
    ⟨prime_4073, by decide, by decide⟩,
    ⟨prime_4079, by decide, by decide⟩,
    ⟨prime_4091, by decide, by decide⟩,
    ⟨prime_4093, by decide, by decide⟩,
    ⟨prime_4099, by decide, by decide⟩,
    ⟨prime_4111, by decide, by decide⟩,
    ⟨prime_4127, by decide, by decide⟩,
    ⟨prime_4129, by decide, by decide⟩,
    ⟨prime_4133, by decide, by decide⟩,
    ⟨prime_4139, by decide, by decide⟩,
    ⟨prime_4153, by decide, by decide⟩,
    ⟨prime_4157, by decide, by decide⟩,
    ⟨prime_4159, by decide, by decide⟩,
    ⟨prime_4177, by decide, by decide⟩,
    ⟨prime_4201, by decide, by decide⟩,
    ⟨prime_4211, by decide, by decide⟩,
    ⟨prime_4217, by decide, by decide⟩
  ⟩

end B008
end Sude.Lucas.Generated
