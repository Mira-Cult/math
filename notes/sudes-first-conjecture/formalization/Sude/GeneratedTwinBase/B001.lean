import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0012

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B001
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_317, by decide, by decide⟩,
    ⟨prime_331, by decide, by decide⟩,
    ⟨prime_337, by decide, by decide⟩,
    ⟨prime_347, by decide, by decide⟩,
    ⟨prime_349, by decide, by decide⟩,
    ⟨prime_353, by decide, by decide⟩,
    ⟨prime_359, by decide, by decide⟩,
    ⟨prime_367, by decide, by decide⟩,
    ⟨prime_373, by decide, by decide⟩,
    ⟨prime_379, by decide, by decide⟩,
    ⟨prime_383, by decide, by decide⟩,
    ⟨prime_389, by decide, by decide⟩,
    ⟨prime_397, by decide, by decide⟩,
    ⟨prime_401, by decide, by decide⟩,
    ⟨prime_409, by decide, by decide⟩,
    ⟨prime_419, by decide, by decide⟩,
    ⟨prime_421, by decide, by decide⟩,
    ⟨prime_431, by decide, by decide⟩,
    ⟨prime_433, by decide, by decide⟩,
    ⟨prime_439, by decide, by decide⟩,
    ⟨prime_443, by decide, by decide⟩,
    ⟨prime_449, by decide, by decide⟩,
    ⟨prime_457, by decide, by decide⟩,
    ⟨prime_461, by decide, by decide⟩,
    ⟨prime_463, by decide, by decide⟩,
    ⟨prime_467, by decide, by decide⟩,
    ⟨prime_479, by decide, by decide⟩,
    ⟨prime_487, by decide, by decide⟩,
    ⟨prime_491, by decide, by decide⟩,
    ⟨prime_499, by decide, by decide⟩,
    ⟨prime_503, by decide, by decide⟩,
    ⟨prime_509, by decide, by decide⟩,
    ⟨prime_521, by decide, by decide⟩,
    ⟨prime_523, by decide, by decide⟩,
    ⟨prime_541, by decide, by decide⟩,
    ⟨prime_547, by decide, by decide⟩,
    ⟨prime_557, by decide, by decide⟩,
    ⟨prime_563, by decide, by decide⟩,
    ⟨prime_569, by decide, by decide⟩,
    ⟨prime_571, by decide, by decide⟩,
    ⟨prime_577, by decide, by decide⟩,
    ⟨prime_587, by decide, by decide⟩,
    ⟨prime_593, by decide, by decide⟩,
    ⟨prime_599, by decide, by decide⟩,
    ⟨prime_601, by decide, by decide⟩,
    ⟨prime_607, by decide, by decide⟩,
    ⟨prime_613, by decide, by decide⟩,
    ⟨prime_617, by decide, by decide⟩,
    ⟨prime_619, by decide, by decide⟩,
    ⟨prime_631, by decide, by decide⟩,
    ⟨prime_641, by decide, by decide⟩,
    ⟨prime_643, by decide, by decide⟩,
    ⟨prime_647, by decide, by decide⟩,
    ⟨prime_653, by decide, by decide⟩,
    ⟨prime_659, by decide, by decide⟩,
    ⟨prime_661, by decide, by decide⟩,
    ⟨prime_673, by decide, by decide⟩,
    ⟨prime_677, by decide, by decide⟩,
    ⟨prime_683, by decide, by decide⟩,
    ⟨prime_691, by decide, by decide⟩,
    ⟨prime_701, by decide, by decide⟩,
    ⟨prime_709, by decide, by decide⟩,
    ⟨prime_719, by decide, by decide⟩,
    ⟨prime_727, by decide, by decide⟩
  ⟩

end B001
end Sude.Lucas.Generated
