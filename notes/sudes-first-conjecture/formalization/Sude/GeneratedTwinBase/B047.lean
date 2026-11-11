import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0075
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0080
import Sude.GeneratedFTT.N0096
import Sude.GeneratedFTT.N0099
import Sude.GeneratedFTT.N0117
import Sude.GeneratedFTT.N0129
import Sude.GeneratedFTT.N0132
import Sude.GeneratedFTT.N0138
import Sude.GeneratedTwinBase.M002
import Sude.GeneratedTwinBase.M003
import Sude.GeneratedTwinBase.B045

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B047
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [27551, 27581, 27583, 27611, 27617, 27631, 27647, 27653, 27673, 27689, 27691, 27697, 27701, 27733, 27737, 27739, 27743, 27749, 27751, 27763, 27767, 27773, 27779, 27791, 27793, 27799, 27803, 27809, 27817, 27823, 27827, 27847, 27851, 27883, 27893, 27901, 27917, 27919, 27941, 27943, 27947, 27953, 27961, 27967, 27983, 27997, 28001, 28019, 28027, 28031, 28051, 28057, 28069, 28081, 28087, 28097, 28099, 28109, 28111, 28123, 28151, 28163, 28181, 28183]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_27551, by decide, by decide⟩,
    ⟨prime_27581, by decide, by decide⟩,
    ⟨prime_27583, by decide, by decide⟩,
    ⟨prime_27611, by decide, by decide⟩,
    ⟨prime_27617, by decide, by decide⟩,
    ⟨prime_27631, by decide, by decide⟩,
    ⟨prime_27647, by decide, by decide⟩,
    ⟨prime_27653, by decide, by decide⟩,
    ⟨prime_27673, by decide, by decide⟩,
    ⟨prime_27689, by decide, by decide⟩,
    ⟨prime_27691, by decide, by decide⟩,
    ⟨prime_27697, by decide, by decide⟩,
    ⟨prime_27701, by decide, by decide⟩,
    ⟨prime_27733, by decide, by decide⟩,
    ⟨prime_27737, by decide, by decide⟩,
    ⟨prime_27739, by decide, by decide⟩,
    ⟨prime_27743, by decide, by decide⟩,
    ⟨prime_27749, by decide, by decide⟩,
    ⟨prime_27751, by decide, by decide⟩,
    ⟨prime_27763, by decide, by decide⟩,
    ⟨prime_27767, by decide, by decide⟩,
    ⟨prime_27773, by decide, by decide⟩,
    ⟨prime_27779, by decide, by decide⟩,
    ⟨prime_27791, by decide, by decide⟩,
    ⟨prime_27793, by decide, by decide⟩,
    ⟨prime_27799, by decide, by decide⟩,
    ⟨prime_27803, by decide, by decide⟩,
    ⟨prime_27809, by decide, by decide⟩,
    ⟨prime_27817, by decide, by decide⟩,
    ⟨prime_27823, by decide, by decide⟩,
    ⟨prime_27827, by decide, by decide⟩,
    ⟨prime_27847, by decide, by decide⟩,
    ⟨prime_27851, by decide, by decide⟩,
    ⟨prime_27883, by decide, by decide⟩,
    ⟨prime_27893, by decide, by decide⟩,
    ⟨prime_27901, by decide, by decide⟩,
    ⟨prime_27917, by decide, by decide⟩,
    ⟨prime_27919, by decide, by decide⟩,
    ⟨prime_27941, by decide, by decide⟩,
    ⟨prime_27943, by decide, by decide⟩,
    ⟨prime_27947, by decide, by decide⟩,
    ⟨prime_27953, by decide, by decide⟩,
    ⟨prime_27961, by decide, by decide⟩,
    ⟨prime_27967, by decide, by decide⟩,
    ⟨prime_27983, by decide, by decide⟩,
    ⟨prime_27997, by decide, by decide⟩,
    ⟨prime_28001, by decide, by decide⟩,
    ⟨prime_28019, by decide, by decide⟩,
    ⟨prime_28027, by decide, by decide⟩,
    ⟨prime_28031, by decide, by decide⟩,
    ⟨prime_28051, by decide, by decide⟩,
    ⟨prime_28057, by decide, by decide⟩,
    ⟨prime_28069, by decide, by decide⟩,
    ⟨prime_28081, by decide, by decide⟩,
    ⟨prime_28087, by decide, by decide⟩,
    ⟨prime_28097, by decide, by decide⟩,
    ⟨prime_28099, by decide, by decide⟩,
    ⟨prime_28109, by decide, by decide⟩,
    ⟨prime_28111, by decide, by decide⟩,
    ⟨prime_28123, by decide, by decide⟩,
    ⟨prime_28151, by decide, by decide⟩,
    ⟨prime_28163, by decide, by decide⟩,
    ⟨prime_28181, by decide, by decide⟩,
    ⟨prime_28183, by decide, by decide⟩
  ⟩

end B047
end Sude.Lucas.Generated
