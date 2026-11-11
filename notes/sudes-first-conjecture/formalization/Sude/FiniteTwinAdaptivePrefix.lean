import Sude.FiniteTwinTakeWhileBase
import Mathlib.Data.Nat.Sqrt

/-! An automatically selected complete prime-base prefix for a compressed
interval scan. The exact scanner lookahead controls the prefix bound. -/
namespace Sude

/-- The exact padded maximum used by the compressed interval specification. -/
def finiteTwinScanLookahead (lo hi : ℕ) : ℕ :=
  strideSixFirst lo + 2 * (3 * strideSixWidth lo hi + 1)

/-- Choosing the integer square root of the padded maximum gives a base bound
whose successor squared safely exceeds that maximum. -/
theorem finite_twin_scan_sqrt_lookahead (lo hi : ℕ) :
    finiteTwinScanLookahead lo hi ≤
      (Nat.sqrt (finiteTwinScanLookahead lo hi) + 1) *
        (Nat.sqrt (finiteTwinScanLookahead lo hi) + 1) := by
  exact Nat.le_of_lt (Nat.lt_succ_sqrt _)

/-- The automatically bounded prefix scan agrees with the exact half-open
segment whenever its required bound lies within the verified base. -/
theorem finite_twin_adaptive_prefix_interval_spec (lo hi : ℕ)
    (hlo : 5 ≤ lo) (hbase : Nat.sqrt (finiteTwinScanLookahead lo hi) ≤ 32768) :
    strideSixCompressedIntervalScan
        (finiteTwinCheckedBase.takeWhile (fun p => p ≤ Nat.sqrt (finiteTwinScanLookahead lo hi))) lo hi =
      (twinPrimeSegment lo hi).card := by
  apply finiteTwinTakeWhile_compressed_interval_spec _ lo hi hbase hlo
  exact finite_twin_scan_sqrt_lookahead lo hi

end Sude
