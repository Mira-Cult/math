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
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0057
import Sude.GeneratedTwinBase.B004

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B006
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_2663, by decide, by decide⟩,
    ⟨prime_2671, by decide, by decide⟩,
    ⟨prime_2677, by decide, by decide⟩,
    ⟨prime_2683, by decide, by decide⟩,
    ⟨prime_2687, by decide, by decide⟩,
    ⟨prime_2689, by decide, by decide⟩,
    ⟨prime_2693, by decide, by decide⟩,
    ⟨prime_2699, by decide, by decide⟩,
    ⟨prime_2707, by decide, by decide⟩,
    ⟨prime_2711, by decide, by decide⟩,
    ⟨prime_2713, by decide, by decide⟩,
    ⟨prime_2719, by decide, by decide⟩,
    ⟨prime_2729, by decide, by decide⟩,
    ⟨prime_2731, by decide, by decide⟩,
    ⟨prime_2741, by decide, by decide⟩,
    ⟨prime_2749, by decide, by decide⟩,
    ⟨prime_2753, by decide, by decide⟩,
    ⟨prime_2767, by decide, by decide⟩,
    ⟨prime_2777, by decide, by decide⟩,
    ⟨prime_2789, by decide, by decide⟩,
    ⟨prime_2791, by decide, by decide⟩,
    ⟨prime_2797, by decide, by decide⟩,
    ⟨prime_2801, by decide, by decide⟩,
    ⟨prime_2803, by decide, by decide⟩,
    ⟨prime_2819, by decide, by decide⟩,
    ⟨prime_2833, by decide, by decide⟩,
    ⟨prime_2837, by decide, by decide⟩,
    ⟨prime_2843, by decide, by decide⟩,
    ⟨prime_2851, by decide, by decide⟩,
    ⟨prime_2857, by decide, by decide⟩,
    ⟨prime_2861, by decide, by decide⟩,
    ⟨prime_2879, by decide, by decide⟩,
    ⟨prime_2887, by decide, by decide⟩,
    ⟨prime_2897, by decide, by decide⟩,
    ⟨prime_2903, by decide, by decide⟩,
    ⟨prime_2909, by decide, by decide⟩,
    ⟨prime_2917, by decide, by decide⟩,
    ⟨prime_2927, by decide, by decide⟩,
    ⟨prime_2939, by decide, by decide⟩,
    ⟨prime_2953, by decide, by decide⟩,
    ⟨prime_2957, by decide, by decide⟩,
    ⟨prime_2963, by decide, by decide⟩,
    ⟨prime_2969, by decide, by decide⟩,
    ⟨prime_2971, by decide, by decide⟩,
    ⟨prime_2999, by decide, by decide⟩,
    ⟨prime_3001, by decide, by decide⟩,
    ⟨prime_3011, by decide, by decide⟩,
    ⟨prime_3019, by decide, by decide⟩,
    ⟨prime_3023, by decide, by decide⟩,
    ⟨prime_3037, by decide, by decide⟩,
    ⟨prime_3041, by decide, by decide⟩,
    ⟨prime_3049, by decide, by decide⟩,
    ⟨prime_3061, by decide, by decide⟩,
    ⟨prime_3067, by decide, by decide⟩,
    ⟨prime_3079, by decide, by decide⟩,
    ⟨prime_3083, by decide, by decide⟩,
    ⟨prime_3089, by decide, by decide⟩,
    ⟨prime_3109, by decide, by decide⟩,
    ⟨prime_3119, by decide, by decide⟩,
    ⟨prime_3121, by decide, by decide⟩,
    ⟨prime_3137, by decide, by decide⟩,
    ⟨prime_3163, by decide, by decide⟩,
    ⟨prime_3167, by decide, by decide⟩,
    ⟨prime_3169, by decide, by decide⟩
  ⟩

end B006
end Sude.Lucas.Generated
