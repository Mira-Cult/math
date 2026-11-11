import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0078
import Sude.GeneratedFTT.N0085
import Sude.GeneratedFTT.N0092
import Sude.GeneratedFTT.N0096
import Sude.GeneratedFTT.N0099
import Sude.GeneratedFTT.N0101
import Sude.GeneratedFTT.N0111
import Sude.GeneratedFTT.N0118
import Sude.GeneratedFTT.N0132
import Sude.GeneratedFTT.N0141
import Sude.GeneratedFTT.N0143
import Sude.GeneratedFTT.N0144
import Sude.GeneratedTwinBase.M001
import Sude.GeneratedTwinBase.B036

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B038
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [21683, 21701, 21713, 21727, 21737, 21739, 21751, 21757, 21767, 21773, 21787, 21799, 21803, 21817, 21821, 21839, 21841, 21851, 21859, 21863, 21871, 21881, 21893, 21911, 21929, 21937, 21943, 21961, 21977, 21991, 21997, 22003, 22013, 22027, 22031, 22037, 22039, 22051, 22063, 22067, 22073, 22079, 22091, 22093, 22109, 22111, 22123, 22129, 22133, 22147, 22153, 22157, 22159, 22171, 22189, 22193, 22229, 22247, 22259, 22271, 22273, 22277, 22279, 22283]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_21683, by decide, by decide⟩,
    ⟨prime_21701, by decide, by decide⟩,
    ⟨prime_21713, by decide, by decide⟩,
    ⟨prime_21727, by decide, by decide⟩,
    ⟨prime_21737, by decide, by decide⟩,
    ⟨prime_21739, by decide, by decide⟩,
    ⟨prime_21751, by decide, by decide⟩,
    ⟨prime_21757, by decide, by decide⟩,
    ⟨prime_21767, by decide, by decide⟩,
    ⟨prime_21773, by decide, by decide⟩,
    ⟨prime_21787, by decide, by decide⟩,
    ⟨prime_21799, by decide, by decide⟩,
    ⟨prime_21803, by decide, by decide⟩,
    ⟨prime_21817, by decide, by decide⟩,
    ⟨prime_21821, by decide, by decide⟩,
    ⟨prime_21839, by decide, by decide⟩,
    ⟨prime_21841, by decide, by decide⟩,
    ⟨prime_21851, by decide, by decide⟩,
    ⟨prime_21859, by decide, by decide⟩,
    ⟨prime_21863, by decide, by decide⟩,
    ⟨prime_21871, by decide, by decide⟩,
    ⟨prime_21881, by decide, by decide⟩,
    ⟨prime_21893, by decide, by decide⟩,
    ⟨prime_21911, by decide, by decide⟩,
    ⟨prime_21929, by decide, by decide⟩,
    ⟨prime_21937, by decide, by decide⟩,
    ⟨prime_21943, by decide, by decide⟩,
    ⟨prime_21961, by decide, by decide⟩,
    ⟨prime_21977, by decide, by decide⟩,
    ⟨prime_21991, by decide, by decide⟩,
    ⟨prime_21997, by decide, by decide⟩,
    ⟨prime_22003, by decide, by decide⟩,
    ⟨prime_22013, by decide, by decide⟩,
    ⟨prime_22027, by decide, by decide⟩,
    ⟨prime_22031, by decide, by decide⟩,
    ⟨prime_22037, by decide, by decide⟩,
    ⟨prime_22039, by decide, by decide⟩,
    ⟨prime_22051, by decide, by decide⟩,
    ⟨prime_22063, by decide, by decide⟩,
    ⟨prime_22067, by decide, by decide⟩,
    ⟨prime_22073, by decide, by decide⟩,
    ⟨prime_22079, by decide, by decide⟩,
    ⟨prime_22091, by decide, by decide⟩,
    ⟨prime_22093, by decide, by decide⟩,
    ⟨prime_22109, by decide, by decide⟩,
    ⟨prime_22111, by decide, by decide⟩,
    ⟨prime_22123, by decide, by decide⟩,
    ⟨prime_22129, by decide, by decide⟩,
    ⟨prime_22133, by decide, by decide⟩,
    ⟨prime_22147, by decide, by decide⟩,
    ⟨prime_22153, by decide, by decide⟩,
    ⟨prime_22157, by decide, by decide⟩,
    ⟨prime_22159, by decide, by decide⟩,
    ⟨prime_22171, by decide, by decide⟩,
    ⟨prime_22189, by decide, by decide⟩,
    ⟨prime_22193, by decide, by decide⟩,
    ⟨prime_22229, by decide, by decide⟩,
    ⟨prime_22247, by decide, by decide⟩,
    ⟨prime_22259, by decide, by decide⟩,
    ⟨prime_22271, by decide, by decide⟩,
    ⟨prime_22273, by decide, by decide⟩,
    ⟨prime_22277, by decide, by decide⟩,
    ⟨prime_22279, by decide, by decide⟩,
    ⟨prime_22283, by decide, by decide⟩
  ⟩

end B038
end Sude.Lucas.Generated
