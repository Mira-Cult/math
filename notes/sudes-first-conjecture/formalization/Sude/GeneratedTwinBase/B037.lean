import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0064
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0079
import Sude.GeneratedFTT.N0080
import Sude.GeneratedFTT.N0081
import Sude.GeneratedFTT.N0082
import Sude.GeneratedFTT.N0090
import Sude.GeneratedFTT.N0107
import Sude.GeneratedFTT.N0110
import Sude.GeneratedFTT.N0114
import Sude.GeneratedFTT.N0118
import Sude.GeneratedFTT.N0119
import Sude.GeneratedFTT.N0121
import Sude.GeneratedFTT.N0122
import Sude.GeneratedFTT.N0129
import Sude.GeneratedFTT.N0133
import Sude.GeneratedFTT.N0136
import Sude.GeneratedFTT.N0149
import Sude.GeneratedTwinBase.M001
import Sude.GeneratedTwinBase.B035

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B037
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [21067, 21089, 21101, 21107, 21121, 21139, 21143, 21149, 21157, 21163, 21169, 21179, 21187, 21191, 21193, 21211, 21221, 21227, 21247, 21269, 21277, 21283, 21313, 21317, 21319, 21323, 21341, 21347, 21377, 21379, 21383, 21391, 21397, 21401, 21407, 21419, 21433, 21467, 21481, 21487, 21491, 21493, 21499, 21503, 21517, 21521, 21523, 21529, 21557, 21559, 21563, 21569, 21577, 21587, 21589, 21599, 21601, 21611, 21613, 21617, 21647, 21649, 21661, 21673]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_21067, by decide, by decide⟩,
    ⟨prime_21089, by decide, by decide⟩,
    ⟨prime_21101, by decide, by decide⟩,
    ⟨prime_21107, by decide, by decide⟩,
    ⟨prime_21121, by decide, by decide⟩,
    ⟨prime_21139, by decide, by decide⟩,
    ⟨prime_21143, by decide, by decide⟩,
    ⟨prime_21149, by decide, by decide⟩,
    ⟨prime_21157, by decide, by decide⟩,
    ⟨prime_21163, by decide, by decide⟩,
    ⟨prime_21169, by decide, by decide⟩,
    ⟨prime_21179, by decide, by decide⟩,
    ⟨prime_21187, by decide, by decide⟩,
    ⟨prime_21191, by decide, by decide⟩,
    ⟨prime_21193, by decide, by decide⟩,
    ⟨prime_21211, by decide, by decide⟩,
    ⟨prime_21221, by decide, by decide⟩,
    ⟨prime_21227, by decide, by decide⟩,
    ⟨prime_21247, by decide, by decide⟩,
    ⟨prime_21269, by decide, by decide⟩,
    ⟨prime_21277, by decide, by decide⟩,
    ⟨prime_21283, by decide, by decide⟩,
    ⟨prime_21313, by decide, by decide⟩,
    ⟨prime_21317, by decide, by decide⟩,
    ⟨prime_21319, by decide, by decide⟩,
    ⟨prime_21323, by decide, by decide⟩,
    ⟨prime_21341, by decide, by decide⟩,
    ⟨prime_21347, by decide, by decide⟩,
    ⟨prime_21377, by decide, by decide⟩,
    ⟨prime_21379, by decide, by decide⟩,
    ⟨prime_21383, by decide, by decide⟩,
    ⟨prime_21391, by decide, by decide⟩,
    ⟨prime_21397, by decide, by decide⟩,
    ⟨prime_21401, by decide, by decide⟩,
    ⟨prime_21407, by decide, by decide⟩,
    ⟨prime_21419, by decide, by decide⟩,
    ⟨prime_21433, by decide, by decide⟩,
    ⟨prime_21467, by decide, by decide⟩,
    ⟨prime_21481, by decide, by decide⟩,
    ⟨prime_21487, by decide, by decide⟩,
    ⟨prime_21491, by decide, by decide⟩,
    ⟨prime_21493, by decide, by decide⟩,
    ⟨prime_21499, by decide, by decide⟩,
    ⟨prime_21503, by decide, by decide⟩,
    ⟨prime_21517, by decide, by decide⟩,
    ⟨prime_21521, by decide, by decide⟩,
    ⟨prime_21523, by decide, by decide⟩,
    ⟨prime_21529, by decide, by decide⟩,
    ⟨prime_21557, by decide, by decide⟩,
    ⟨prime_21559, by decide, by decide⟩,
    ⟨prime_21563, by decide, by decide⟩,
    ⟨prime_21569, by decide, by decide⟩,
    ⟨prime_21577, by decide, by decide⟩,
    ⟨prime_21587, by decide, by decide⟩,
    ⟨prime_21589, by decide, by decide⟩,
    ⟨prime_21599, by decide, by decide⟩,
    ⟨prime_21601, by decide, by decide⟩,
    ⟨prime_21611, by decide, by decide⟩,
    ⟨prime_21613, by decide, by decide⟩,
    ⟨prime_21617, by decide, by decide⟩,
    ⟨prime_21647, by decide, by decide⟩,
    ⟨prime_21649, by decide, by decide⟩,
    ⟨prime_21661, by decide, by decide⟩,
    ⟨prime_21673, by decide, by decide⟩
  ⟩

end B037
end Sude.Lucas.Generated
