import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
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
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0078
import Sude.GeneratedTwinBase.B003

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B005
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_2137, by decide, by decide⟩,
    ⟨prime_2141, by decide, by decide⟩,
    ⟨prime_2143, by decide, by decide⟩,
    ⟨prime_2153, by decide, by decide⟩,
    ⟨prime_2161, by decide, by decide⟩,
    ⟨prime_2179, by decide, by decide⟩,
    ⟨prime_2203, by decide, by decide⟩,
    ⟨prime_2207, by decide, by decide⟩,
    ⟨prime_2213, by decide, by decide⟩,
    ⟨prime_2221, by decide, by decide⟩,
    ⟨prime_2237, by decide, by decide⟩,
    ⟨prime_2239, by decide, by decide⟩,
    ⟨prime_2243, by decide, by decide⟩,
    ⟨prime_2251, by decide, by decide⟩,
    ⟨prime_2267, by decide, by decide⟩,
    ⟨prime_2269, by decide, by decide⟩,
    ⟨prime_2273, by decide, by decide⟩,
    ⟨prime_2281, by decide, by decide⟩,
    ⟨prime_2287, by decide, by decide⟩,
    ⟨prime_2293, by decide, by decide⟩,
    ⟨prime_2297, by decide, by decide⟩,
    ⟨prime_2309, by decide, by decide⟩,
    ⟨prime_2311, by decide, by decide⟩,
    ⟨prime_2333, by decide, by decide⟩,
    ⟨prime_2339, by decide, by decide⟩,
    ⟨prime_2341, by decide, by decide⟩,
    ⟨prime_2347, by decide, by decide⟩,
    ⟨prime_2351, by decide, by decide⟩,
    ⟨prime_2357, by decide, by decide⟩,
    ⟨prime_2371, by decide, by decide⟩,
    ⟨prime_2377, by decide, by decide⟩,
    ⟨prime_2381, by decide, by decide⟩,
    ⟨prime_2383, by decide, by decide⟩,
    ⟨prime_2389, by decide, by decide⟩,
    ⟨prime_2393, by decide, by decide⟩,
    ⟨prime_2399, by decide, by decide⟩,
    ⟨prime_2411, by decide, by decide⟩,
    ⟨prime_2417, by decide, by decide⟩,
    ⟨prime_2423, by decide, by decide⟩,
    ⟨prime_2437, by decide, by decide⟩,
    ⟨prime_2441, by decide, by decide⟩,
    ⟨prime_2447, by decide, by decide⟩,
    ⟨prime_2459, by decide, by decide⟩,
    ⟨prime_2467, by decide, by decide⟩,
    ⟨prime_2473, by decide, by decide⟩,
    ⟨prime_2477, by decide, by decide⟩,
    ⟨prime_2503, by decide, by decide⟩,
    ⟨prime_2521, by decide, by decide⟩,
    ⟨prime_2531, by decide, by decide⟩,
    ⟨prime_2539, by decide, by decide⟩,
    ⟨prime_2543, by decide, by decide⟩,
    ⟨prime_2549, by decide, by decide⟩,
    ⟨prime_2551, by decide, by decide⟩,
    ⟨prime_2557, by decide, by decide⟩,
    ⟨prime_2579, by decide, by decide⟩,
    ⟨prime_2591, by decide, by decide⟩,
    ⟨prime_2593, by decide, by decide⟩,
    ⟨prime_2609, by decide, by decide⟩,
    ⟨prime_2617, by decide, by decide⟩,
    ⟨prime_2621, by decide, by decide⟩,
    ⟨prime_2633, by decide, by decide⟩,
    ⟨prime_2647, by decide, by decide⟩,
    ⟨prime_2657, by decide, by decide⟩,
    ⟨prime_2659, by decide, by decide⟩
  ⟩

end B005
end Sude.Lucas.Generated
