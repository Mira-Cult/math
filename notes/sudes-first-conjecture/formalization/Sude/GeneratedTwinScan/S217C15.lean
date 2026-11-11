import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S217C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21379)) 457048109 457080877 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 457048109 457080877).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21379 457048109 457080877
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21380)) 457080877 457113645 = 96 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 457080877 457113645).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21380 457080877 457113645
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21380)) 457113645 457146413 = 92 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 457113645 457146413).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21380 457113645 457146413
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21381)) 457146413 457179181 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 457146413 457179181).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21381 457146413 457179181
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 457048109 457113645).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 457048109 ≤ 457080877)
    (by decide : 457080877 ≤ 457113645) block0 block1

theorem join_0_1 : (twinPrimeSegment 457113645 457179181).card = 193 := by
  simpa using combineTwinPrimeSegments (by decide : 457113645 ≤ 457146413)
    (by decide : 457146413 ≤ 457179181) block2 block3

theorem join_1_0 : (twinPrimeSegment 457048109 457179181).card = 399 := by
  simpa using combineTwinPrimeSegments (by decide : 457048109 ≤ 457113645)
    (by decide : 457113645 ≤ 457179181) join_0_0 join_0_1

theorem total : (twinPrimeSegment 457048109 457179181).card = 399 := join_1_0

end S217C15
end Sude.GeneratedTwinScan
