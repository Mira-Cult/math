import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0009
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
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0078
import Sude.GeneratedFTT.N0085
import Sude.GeneratedFTT.N0090
import Sude.GeneratedFTT.N0101
import Sude.GeneratedFTT.N0119
import Sude.GeneratedFTT.N0146
import Sude.GeneratedFTT.N0149
import Sude.GeneratedTwinBase.B012

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B014
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [6983, 6991, 6997, 7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393, 7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_6983, by decide, by decide⟩,
    ⟨prime_6991, by decide, by decide⟩,
    ⟨prime_6997, by decide, by decide⟩,
    ⟨prime_7001, by decide, by decide⟩,
    ⟨prime_7013, by decide, by decide⟩,
    ⟨prime_7019, by decide, by decide⟩,
    ⟨prime_7027, by decide, by decide⟩,
    ⟨prime_7039, by decide, by decide⟩,
    ⟨prime_7043, by decide, by decide⟩,
    ⟨prime_7057, by decide, by decide⟩,
    ⟨prime_7069, by decide, by decide⟩,
    ⟨prime_7079, by decide, by decide⟩,
    ⟨prime_7103, by decide, by decide⟩,
    ⟨prime_7109, by decide, by decide⟩,
    ⟨prime_7121, by decide, by decide⟩,
    ⟨prime_7127, by decide, by decide⟩,
    ⟨prime_7129, by decide, by decide⟩,
    ⟨prime_7151, by decide, by decide⟩,
    ⟨prime_7159, by decide, by decide⟩,
    ⟨prime_7177, by decide, by decide⟩,
    ⟨prime_7187, by decide, by decide⟩,
    ⟨prime_7193, by decide, by decide⟩,
    ⟨prime_7207, by decide, by decide⟩,
    ⟨prime_7211, by decide, by decide⟩,
    ⟨prime_7213, by decide, by decide⟩,
    ⟨prime_7219, by decide, by decide⟩,
    ⟨prime_7229, by decide, by decide⟩,
    ⟨prime_7237, by decide, by decide⟩,
    ⟨prime_7243, by decide, by decide⟩,
    ⟨prime_7247, by decide, by decide⟩,
    ⟨prime_7253, by decide, by decide⟩,
    ⟨prime_7283, by decide, by decide⟩,
    ⟨prime_7297, by decide, by decide⟩,
    ⟨prime_7307, by decide, by decide⟩,
    ⟨prime_7309, by decide, by decide⟩,
    ⟨prime_7321, by decide, by decide⟩,
    ⟨prime_7331, by decide, by decide⟩,
    ⟨prime_7333, by decide, by decide⟩,
    ⟨prime_7349, by decide, by decide⟩,
    ⟨prime_7351, by decide, by decide⟩,
    ⟨prime_7369, by decide, by decide⟩,
    ⟨prime_7393, by decide, by decide⟩,
    ⟨prime_7411, by decide, by decide⟩,
    ⟨prime_7417, by decide, by decide⟩,
    ⟨prime_7433, by decide, by decide⟩,
    ⟨prime_7451, by decide, by decide⟩,
    ⟨prime_7457, by decide, by decide⟩,
    ⟨prime_7459, by decide, by decide⟩,
    ⟨prime_7477, by decide, by decide⟩,
    ⟨prime_7481, by decide, by decide⟩,
    ⟨prime_7487, by decide, by decide⟩,
    ⟨prime_7489, by decide, by decide⟩,
    ⟨prime_7499, by decide, by decide⟩,
    ⟨prime_7507, by decide, by decide⟩,
    ⟨prime_7517, by decide, by decide⟩,
    ⟨prime_7523, by decide, by decide⟩,
    ⟨prime_7529, by decide, by decide⟩,
    ⟨prime_7537, by decide, by decide⟩,
    ⟨prime_7541, by decide, by decide⟩,
    ⟨prime_7547, by decide, by decide⟩,
    ⟨prime_7549, by decide, by decide⟩,
    ⟨prime_7559, by decide, by decide⟩,
    ⟨prime_7561, by decide, by decide⟩,
    ⟨prime_7573, by decide, by decide⟩
  ⟩

end B014
end Sude.Lucas.Generated
