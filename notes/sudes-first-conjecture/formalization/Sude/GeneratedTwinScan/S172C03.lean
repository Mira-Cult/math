import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S172C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19003)) 361103405 361136173 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 361103405 361136173).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19003 361103405 361136173
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19004)) 361136173 361168941 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 361136173 361168941).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19004 361136173 361168941
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19005)) 361168941 361201709 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 361168941 361201709).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19005 361168941 361201709
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19006)) 361201709 361234477 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 361201709 361234477).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19006 361201709 361234477
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 361103405 361168941).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 361103405 ≤ 361136173)
    (by decide : 361136173 ≤ 361168941) block0 block1

theorem join_0_1 : (twinPrimeSegment 361168941 361234477).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 361168941 ≤ 361201709)
    (by decide : 361201709 ≤ 361234477) block2 block3

theorem join_1_0 : (twinPrimeSegment 361103405 361234477).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 361103405 ≤ 361168941)
    (by decide : 361168941 ≤ 361234477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 361103405 361234477).card = 432 := join_1_0

end S172C03
end Sude.GeneratedTwinScan
