import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0082
import Sude.GeneratedFTT.N0090
import Sude.GeneratedFTT.N0140
import Sude.GeneratedTwinBase.B011

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B013
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [6397, 6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_6397, by decide, by decide⟩,
    ⟨prime_6421, by decide, by decide⟩,
    ⟨prime_6427, by decide, by decide⟩,
    ⟨prime_6449, by decide, by decide⟩,
    ⟨prime_6451, by decide, by decide⟩,
    ⟨prime_6469, by decide, by decide⟩,
    ⟨prime_6473, by decide, by decide⟩,
    ⟨prime_6481, by decide, by decide⟩,
    ⟨prime_6491, by decide, by decide⟩,
    ⟨prime_6521, by decide, by decide⟩,
    ⟨prime_6529, by decide, by decide⟩,
    ⟨prime_6547, by decide, by decide⟩,
    ⟨prime_6551, by decide, by decide⟩,
    ⟨prime_6553, by decide, by decide⟩,
    ⟨prime_6563, by decide, by decide⟩,
    ⟨prime_6569, by decide, by decide⟩,
    ⟨prime_6571, by decide, by decide⟩,
    ⟨prime_6577, by decide, by decide⟩,
    ⟨prime_6581, by decide, by decide⟩,
    ⟨prime_6599, by decide, by decide⟩,
    ⟨prime_6607, by decide, by decide⟩,
    ⟨prime_6619, by decide, by decide⟩,
    ⟨prime_6637, by decide, by decide⟩,
    ⟨prime_6653, by decide, by decide⟩,
    ⟨prime_6659, by decide, by decide⟩,
    ⟨prime_6661, by decide, by decide⟩,
    ⟨prime_6673, by decide, by decide⟩,
    ⟨prime_6679, by decide, by decide⟩,
    ⟨prime_6689, by decide, by decide⟩,
    ⟨prime_6691, by decide, by decide⟩,
    ⟨prime_6701, by decide, by decide⟩,
    ⟨prime_6703, by decide, by decide⟩,
    ⟨prime_6709, by decide, by decide⟩,
    ⟨prime_6719, by decide, by decide⟩,
    ⟨prime_6733, by decide, by decide⟩,
    ⟨prime_6737, by decide, by decide⟩,
    ⟨prime_6761, by decide, by decide⟩,
    ⟨prime_6763, by decide, by decide⟩,
    ⟨prime_6779, by decide, by decide⟩,
    ⟨prime_6781, by decide, by decide⟩,
    ⟨prime_6791, by decide, by decide⟩,
    ⟨prime_6793, by decide, by decide⟩,
    ⟨prime_6803, by decide, by decide⟩,
    ⟨prime_6823, by decide, by decide⟩,
    ⟨prime_6827, by decide, by decide⟩,
    ⟨prime_6829, by decide, by decide⟩,
    ⟨prime_6833, by decide, by decide⟩,
    ⟨prime_6841, by decide, by decide⟩,
    ⟨prime_6857, by decide, by decide⟩,
    ⟨prime_6863, by decide, by decide⟩,
    ⟨prime_6869, by decide, by decide⟩,
    ⟨prime_6871, by decide, by decide⟩,
    ⟨prime_6883, by decide, by decide⟩,
    ⟨prime_6899, by decide, by decide⟩,
    ⟨prime_6907, by decide, by decide⟩,
    ⟨prime_6911, by decide, by decide⟩,
    ⟨prime_6917, by decide, by decide⟩,
    ⟨prime_6947, by decide, by decide⟩,
    ⟨prime_6949, by decide, by decide⟩,
    ⟨prime_6959, by decide, by decide⟩,
    ⟨prime_6961, by decide, by decide⟩,
    ⟨prime_6967, by decide, by decide⟩,
    ⟨prime_6971, by decide, by decide⟩,
    ⟨prime_6977, by decide, by decide⟩
  ⟩

end B013
end Sude.Lucas.Generated
