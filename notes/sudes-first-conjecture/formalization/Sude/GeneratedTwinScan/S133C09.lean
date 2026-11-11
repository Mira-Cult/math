import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S133C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16737)) 280100909 280133677 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 280100909 280133677).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16737 280100909 280133677
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16738)) 280133677 280166445 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 280133677 280166445).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16738 280133677 280166445
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16739)) 280166445 280199213 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 280166445 280199213).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16739 280166445 280199213
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16740)) 280199213 280231981 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 280199213 280231981).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16740 280199213 280231981
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 280100909 280166445).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 280100909 ≤ 280133677)
    (by decide : 280133677 ≤ 280166445) block0 block1

theorem join_0_1 : (twinPrimeSegment 280166445 280231981).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 280166445 ≤ 280199213)
    (by decide : 280199213 ≤ 280231981) block2 block3

theorem join_1_0 : (twinPrimeSegment 280100909 280231981).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 280100909 ≤ 280166445)
    (by decide : 280166445 ≤ 280231981) join_0_0 join_0_1

theorem total : (twinPrimeSegment 280100909 280231981).card = 439 := join_1_0

end S133C09
end Sude.GeneratedTwinScan
