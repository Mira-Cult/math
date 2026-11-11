import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0080
import Sude.GeneratedFTT.N0086
import Sude.GeneratedFTT.N0098
import Sude.GeneratedFTT.N0108
import Sude.GeneratedFTT.N0116
import Sude.GeneratedFTT.N0121
import Sude.GeneratedFTT.N0147
import Sude.GeneratedTwinBase.M000
import Sude.GeneratedTwinBase.B015

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B017
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [8741, 8747, 8753, 8761, 8779, 8783, 8803, 8807, 8819, 8821, 8831, 8837, 8839, 8849, 8861, 8863, 8867, 8887, 8893, 8923, 8929, 8933, 8941, 8951, 8963, 8969, 8971, 8999, 9001, 9007, 9011, 9013, 9029, 9041, 9043, 9049, 9059, 9067, 9091, 9103, 9109, 9127, 9133, 9137, 9151, 9157, 9161, 9173, 9181, 9187, 9199, 9203, 9209, 9221, 9227, 9239, 9241, 9257, 9277, 9281, 9283, 9293, 9311, 9319]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_8741, by decide, by decide⟩,
    ⟨prime_8747, by decide, by decide⟩,
    ⟨prime_8753, by decide, by decide⟩,
    ⟨prime_8761, by decide, by decide⟩,
    ⟨prime_8779, by decide, by decide⟩,
    ⟨prime_8783, by decide, by decide⟩,
    ⟨prime_8803, by decide, by decide⟩,
    ⟨prime_8807, by decide, by decide⟩,
    ⟨prime_8819, by decide, by decide⟩,
    ⟨prime_8821, by decide, by decide⟩,
    ⟨prime_8831, by decide, by decide⟩,
    ⟨prime_8837, by decide, by decide⟩,
    ⟨prime_8839, by decide, by decide⟩,
    ⟨prime_8849, by decide, by decide⟩,
    ⟨prime_8861, by decide, by decide⟩,
    ⟨prime_8863, by decide, by decide⟩,
    ⟨prime_8867, by decide, by decide⟩,
    ⟨prime_8887, by decide, by decide⟩,
    ⟨prime_8893, by decide, by decide⟩,
    ⟨prime_8923, by decide, by decide⟩,
    ⟨prime_8929, by decide, by decide⟩,
    ⟨prime_8933, by decide, by decide⟩,
    ⟨prime_8941, by decide, by decide⟩,
    ⟨prime_8951, by decide, by decide⟩,
    ⟨prime_8963, by decide, by decide⟩,
    ⟨prime_8969, by decide, by decide⟩,
    ⟨prime_8971, by decide, by decide⟩,
    ⟨prime_8999, by decide, by decide⟩,
    ⟨prime_9001, by decide, by decide⟩,
    ⟨prime_9007, by decide, by decide⟩,
    ⟨prime_9011, by decide, by decide⟩,
    ⟨prime_9013, by decide, by decide⟩,
    ⟨prime_9029, by decide, by decide⟩,
    ⟨prime_9041, by decide, by decide⟩,
    ⟨prime_9043, by decide, by decide⟩,
    ⟨prime_9049, by decide, by decide⟩,
    ⟨prime_9059, by decide, by decide⟩,
    ⟨prime_9067, by decide, by decide⟩,
    ⟨prime_9091, by decide, by decide⟩,
    ⟨prime_9103, by decide, by decide⟩,
    ⟨prime_9109, by decide, by decide⟩,
    ⟨prime_9127, by decide, by decide⟩,
    ⟨prime_9133, by decide, by decide⟩,
    ⟨prime_9137, by decide, by decide⟩,
    ⟨prime_9151, by decide, by decide⟩,
    ⟨prime_9157, by decide, by decide⟩,
    ⟨prime_9161, by decide, by decide⟩,
    ⟨prime_9173, by decide, by decide⟩,
    ⟨prime_9181, by decide, by decide⟩,
    ⟨prime_9187, by decide, by decide⟩,
    ⟨prime_9199, by decide, by decide⟩,
    ⟨prime_9203, by decide, by decide⟩,
    ⟨prime_9209, by decide, by decide⟩,
    ⟨prime_9221, by decide, by decide⟩,
    ⟨prime_9227, by decide, by decide⟩,
    ⟨prime_9239, by decide, by decide⟩,
    ⟨prime_9241, by decide, by decide⟩,
    ⟨prime_9257, by decide, by decide⟩,
    ⟨prime_9277, by decide, by decide⟩,
    ⟨prime_9281, by decide, by decide⟩,
    ⟨prime_9283, by decide, by decide⟩,
    ⟨prime_9293, by decide, by decide⟩,
    ⟨prime_9311, by decide, by decide⟩,
    ⟨prime_9319, by decide, by decide⟩
  ⟩

end B017
end Sude.Lucas.Generated
