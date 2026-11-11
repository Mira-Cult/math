import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0053
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0074
import Sude.GeneratedFTT.N0080
import Sude.GeneratedFTT.N0086
import Sude.GeneratedFTT.N0090
import Sude.GeneratedFTT.N0094
import Sude.GeneratedFTT.N0100
import Sude.GeneratedFTT.N0107
import Sude.GeneratedFTT.N0115
import Sude.GeneratedFTT.N0121
import Sude.GeneratedFTT.N0133
import Sude.GeneratedFTT.N0134
import Sude.GeneratedFTT.N0138
import Sude.GeneratedFTT.N0143
import Sude.GeneratedTwinBase.M001
import Sude.GeneratedTwinBase.B038

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B040
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [22963, 22973, 22993, 23003, 23011, 23017, 23021, 23027, 23029, 23039, 23041, 23053, 23057, 23059, 23063, 23071, 23081, 23087, 23099, 23117, 23131, 23143, 23159, 23167, 23173, 23189, 23197, 23201, 23203, 23209, 23227, 23251, 23269, 23279, 23291, 23293, 23297, 23311, 23321, 23327, 23333, 23339, 23357, 23369, 23371, 23399, 23417, 23431, 23447, 23459, 23473, 23497, 23509, 23531, 23537, 23539, 23549, 23557, 23561, 23563, 23567, 23581, 23593, 23599]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_22963, by decide, by decide⟩,
    ⟨prime_22973, by decide, by decide⟩,
    ⟨prime_22993, by decide, by decide⟩,
    ⟨prime_23003, by decide, by decide⟩,
    ⟨prime_23011, by decide, by decide⟩,
    ⟨prime_23017, by decide, by decide⟩,
    ⟨prime_23021, by decide, by decide⟩,
    ⟨prime_23027, by decide, by decide⟩,
    ⟨prime_23029, by decide, by decide⟩,
    ⟨prime_23039, by decide, by decide⟩,
    ⟨prime_23041, by decide, by decide⟩,
    ⟨prime_23053, by decide, by decide⟩,
    ⟨prime_23057, by decide, by decide⟩,
    ⟨prime_23059, by decide, by decide⟩,
    ⟨prime_23063, by decide, by decide⟩,
    ⟨prime_23071, by decide, by decide⟩,
    ⟨prime_23081, by decide, by decide⟩,
    ⟨prime_23087, by decide, by decide⟩,
    ⟨prime_23099, by decide, by decide⟩,
    ⟨prime_23117, by decide, by decide⟩,
    ⟨prime_23131, by decide, by decide⟩,
    ⟨prime_23143, by decide, by decide⟩,
    ⟨prime_23159, by decide, by decide⟩,
    ⟨prime_23167, by decide, by decide⟩,
    ⟨prime_23173, by decide, by decide⟩,
    ⟨prime_23189, by decide, by decide⟩,
    ⟨prime_23197, by decide, by decide⟩,
    ⟨prime_23201, by decide, by decide⟩,
    ⟨prime_23203, by decide, by decide⟩,
    ⟨prime_23209, by decide, by decide⟩,
    ⟨prime_23227, by decide, by decide⟩,
    ⟨prime_23251, by decide, by decide⟩,
    ⟨prime_23269, by decide, by decide⟩,
    ⟨prime_23279, by decide, by decide⟩,
    ⟨prime_23291, by decide, by decide⟩,
    ⟨prime_23293, by decide, by decide⟩,
    ⟨prime_23297, by decide, by decide⟩,
    ⟨prime_23311, by decide, by decide⟩,
    ⟨prime_23321, by decide, by decide⟩,
    ⟨prime_23327, by decide, by decide⟩,
    ⟨prime_23333, by decide, by decide⟩,
    ⟨prime_23339, by decide, by decide⟩,
    ⟨prime_23357, by decide, by decide⟩,
    ⟨prime_23369, by decide, by decide⟩,
    ⟨prime_23371, by decide, by decide⟩,
    ⟨prime_23399, by decide, by decide⟩,
    ⟨prime_23417, by decide, by decide⟩,
    ⟨prime_23431, by decide, by decide⟩,
    ⟨prime_23447, by decide, by decide⟩,
    ⟨prime_23459, by decide, by decide⟩,
    ⟨prime_23473, by decide, by decide⟩,
    ⟨prime_23497, by decide, by decide⟩,
    ⟨prime_23509, by decide, by decide⟩,
    ⟨prime_23531, by decide, by decide⟩,
    ⟨prime_23537, by decide, by decide⟩,
    ⟨prime_23539, by decide, by decide⟩,
    ⟨prime_23549, by decide, by decide⟩,
    ⟨prime_23557, by decide, by decide⟩,
    ⟨prime_23561, by decide, by decide⟩,
    ⟨prime_23563, by decide, by decide⟩,
    ⟨prime_23567, by decide, by decide⟩,
    ⟨prime_23581, by decide, by decide⟩,
    ⟨prime_23593, by decide, by decide⟩,
    ⟨prime_23599, by decide, by decide⟩
  ⟩

end B040
end Sude.Lucas.Generated
