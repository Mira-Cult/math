import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S174C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19106)) 365035565 365068333 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 365035565 365068333).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19106 365035565 365068333
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19107)) 365068333 365101101 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 365068333 365101101).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19107 365068333 365101101
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19108)) 365101101 365133869 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 365101101 365133869).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19108 365101101 365133869
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19109)) 365133869 365166637 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 365133869 365166637).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19109 365133869 365166637
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 365035565 365101101).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 365035565 ≤ 365068333)
    (by decide : 365068333 ≤ 365101101) block0 block1

theorem join_0_1 : (twinPrimeSegment 365101101 365166637).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 365101101 ≤ 365133869)
    (by decide : 365133869 ≤ 365166637) block2 block3

theorem join_1_0 : (twinPrimeSegment 365035565 365166637).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 365035565 ≤ 365101101)
    (by decide : 365101101 ≤ 365166637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 365035565 365166637).card = 441 := join_1_0

end S174C01
end Sude.GeneratedTwinScan
