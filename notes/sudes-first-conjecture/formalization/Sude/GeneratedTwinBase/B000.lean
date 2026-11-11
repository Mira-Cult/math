import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0006

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B000
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_3, by decide, by decide⟩,
    ⟨prime_5, by decide, by decide⟩,
    ⟨prime_7, by decide, by decide⟩,
    ⟨prime_11, by decide, by decide⟩,
    ⟨prime_13, by decide, by decide⟩,
    ⟨prime_17, by decide, by decide⟩,
    ⟨prime_19, by decide, by decide⟩,
    ⟨prime_23, by decide, by decide⟩,
    ⟨prime_29, by decide, by decide⟩,
    ⟨prime_31, by decide, by decide⟩,
    ⟨prime_37, by decide, by decide⟩,
    ⟨prime_41, by decide, by decide⟩,
    ⟨prime_43, by decide, by decide⟩,
    ⟨prime_47, by decide, by decide⟩,
    ⟨prime_53, by decide, by decide⟩,
    ⟨prime_59, by decide, by decide⟩,
    ⟨prime_61, by decide, by decide⟩,
    ⟨prime_67, by decide, by decide⟩,
    ⟨prime_71, by decide, by decide⟩,
    ⟨prime_73, by decide, by decide⟩,
    ⟨prime_79, by decide, by decide⟩,
    ⟨prime_83, by decide, by decide⟩,
    ⟨prime_89, by decide, by decide⟩,
    ⟨prime_97, by decide, by decide⟩,
    ⟨prime_101, by decide, by decide⟩,
    ⟨prime_103, by decide, by decide⟩,
    ⟨prime_107, by decide, by decide⟩,
    ⟨prime_109, by decide, by decide⟩,
    ⟨prime_113, by decide, by decide⟩,
    ⟨prime_127, by decide, by decide⟩,
    ⟨prime_131, by decide, by decide⟩,
    ⟨prime_137, by decide, by decide⟩,
    ⟨prime_139, by decide, by decide⟩,
    ⟨prime_149, by decide, by decide⟩,
    ⟨prime_151, by decide, by decide⟩,
    ⟨prime_157, by decide, by decide⟩,
    ⟨prime_163, by decide, by decide⟩,
    ⟨prime_167, by decide, by decide⟩,
    ⟨prime_173, by decide, by decide⟩,
    ⟨prime_179, by decide, by decide⟩,
    ⟨prime_181, by decide, by decide⟩,
    ⟨prime_191, by decide, by decide⟩,
    ⟨prime_193, by decide, by decide⟩,
    ⟨prime_197, by decide, by decide⟩,
    ⟨prime_199, by decide, by decide⟩,
    ⟨prime_211, by decide, by decide⟩,
    ⟨prime_223, by decide, by decide⟩,
    ⟨prime_227, by decide, by decide⟩,
    ⟨prime_229, by decide, by decide⟩,
    ⟨prime_233, by decide, by decide⟩,
    ⟨prime_239, by decide, by decide⟩,
    ⟨prime_241, by decide, by decide⟩,
    ⟨prime_251, by decide, by decide⟩,
    ⟨prime_257, by decide, by decide⟩,
    ⟨prime_263, by decide, by decide⟩,
    ⟨prime_269, by decide, by decide⟩,
    ⟨prime_271, by decide, by decide⟩,
    ⟨prime_277, by decide, by decide⟩,
    ⟨prime_281, by decide, by decide⟩,
    ⟨prime_283, by decide, by decide⟩,
    ⟨prime_293, by decide, by decide⟩,
    ⟨prime_307, by decide, by decide⟩,
    ⟨prime_311, by decide, by decide⟩,
    ⟨prime_313, by decide, by decide⟩
  ⟩

end B000
end Sude.Lucas.Generated
