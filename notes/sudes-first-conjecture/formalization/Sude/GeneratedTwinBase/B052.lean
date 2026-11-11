import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0082
import Sude.GeneratedFTT.N0092
import Sude.GeneratedFTT.N0095
import Sude.GeneratedFTT.N0102
import Sude.GeneratedFTT.N0108
import Sude.GeneratedFTT.N0112
import Sude.GeneratedFTT.N0114
import Sude.GeneratedFTT.N0118
import Sude.GeneratedFTT.N0130
import Sude.GeneratedFTT.N0140
import Sude.GeneratedFTT.N0142
import Sude.GeneratedFTT.N0149
import Sude.GeneratedTwinBase.M003
import Sude.GeneratedTwinBase.B050

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B052
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [30871, 30881, 30893, 30911, 30931, 30937, 30941, 30949, 30971, 30977, 30983, 31013, 31019, 31033, 31039, 31051, 31063, 31069, 31079, 31081, 31091, 31121, 31123, 31139, 31147, 31151, 31153, 31159, 31177, 31181, 31183, 31189, 31193, 31219, 31223, 31231, 31237, 31247, 31249, 31253, 31259, 31267, 31271, 31277, 31307, 31319, 31321, 31327, 31333, 31337, 31357, 31379, 31387, 31391, 31393, 31397, 31469, 31477, 31481, 31489, 31511, 31513, 31517, 31531]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_30871, by decide, by decide⟩,
    ⟨prime_30881, by decide, by decide⟩,
    ⟨prime_30893, by decide, by decide⟩,
    ⟨prime_30911, by decide, by decide⟩,
    ⟨prime_30931, by decide, by decide⟩,
    ⟨prime_30937, by decide, by decide⟩,
    ⟨prime_30941, by decide, by decide⟩,
    ⟨prime_30949, by decide, by decide⟩,
    ⟨prime_30971, by decide, by decide⟩,
    ⟨prime_30977, by decide, by decide⟩,
    ⟨prime_30983, by decide, by decide⟩,
    ⟨prime_31013, by decide, by decide⟩,
    ⟨prime_31019, by decide, by decide⟩,
    ⟨prime_31033, by decide, by decide⟩,
    ⟨prime_31039, by decide, by decide⟩,
    ⟨prime_31051, by decide, by decide⟩,
    ⟨prime_31063, by decide, by decide⟩,
    ⟨prime_31069, by decide, by decide⟩,
    ⟨prime_31079, by decide, by decide⟩,
    ⟨prime_31081, by decide, by decide⟩,
    ⟨prime_31091, by decide, by decide⟩,
    ⟨prime_31121, by decide, by decide⟩,
    ⟨prime_31123, by decide, by decide⟩,
    ⟨prime_31139, by decide, by decide⟩,
    ⟨prime_31147, by decide, by decide⟩,
    ⟨prime_31151, by decide, by decide⟩,
    ⟨prime_31153, by decide, by decide⟩,
    ⟨prime_31159, by decide, by decide⟩,
    ⟨prime_31177, by decide, by decide⟩,
    ⟨prime_31181, by decide, by decide⟩,
    ⟨prime_31183, by decide, by decide⟩,
    ⟨prime_31189, by decide, by decide⟩,
    ⟨prime_31193, by decide, by decide⟩,
    ⟨prime_31219, by decide, by decide⟩,
    ⟨prime_31223, by decide, by decide⟩,
    ⟨prime_31231, by decide, by decide⟩,
    ⟨prime_31237, by decide, by decide⟩,
    ⟨prime_31247, by decide, by decide⟩,
    ⟨prime_31249, by decide, by decide⟩,
    ⟨prime_31253, by decide, by decide⟩,
    ⟨prime_31259, by decide, by decide⟩,
    ⟨prime_31267, by decide, by decide⟩,
    ⟨prime_31271, by decide, by decide⟩,
    ⟨prime_31277, by decide, by decide⟩,
    ⟨prime_31307, by decide, by decide⟩,
    ⟨prime_31319, by decide, by decide⟩,
    ⟨prime_31321, by decide, by decide⟩,
    ⟨prime_31327, by decide, by decide⟩,
    ⟨prime_31333, by decide, by decide⟩,
    ⟨prime_31337, by decide, by decide⟩,
    ⟨prime_31357, by decide, by decide⟩,
    ⟨prime_31379, by decide, by decide⟩,
    ⟨prime_31387, by decide, by decide⟩,
    ⟨prime_31391, by decide, by decide⟩,
    ⟨prime_31393, by decide, by decide⟩,
    ⟨prime_31397, by decide, by decide⟩,
    ⟨prime_31469, by decide, by decide⟩,
    ⟨prime_31477, by decide, by decide⟩,
    ⟨prime_31481, by decide, by decide⟩,
    ⟨prime_31489, by decide, by decide⟩,
    ⟨prime_31511, by decide, by decide⟩,
    ⟨prime_31513, by decide, by decide⟩,
    ⟨prime_31517, by decide, by decide⟩,
    ⟨prime_31531, by decide, by decide⟩
  ⟩

end B052
end Sude.Lucas.Generated
