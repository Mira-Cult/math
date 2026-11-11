import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S133C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16701)) 278921261 278954029 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 278921261 278954029).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16701 278921261 278954029
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16702)) 278954029 278986797 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 278954029 278986797).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16702 278954029 278986797
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16703)) 278986797 279019565 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 278986797 279019565).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16703 278986797 279019565
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16704)) 279019565 279052333 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 279019565 279052333).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16704 279019565 279052333
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 278921261 278986797).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 278921261 ≤ 278954029)
    (by decide : 278954029 ≤ 278986797) block0 block1

theorem join_0_1 : (twinPrimeSegment 278986797 279052333).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 278986797 ≤ 279019565)
    (by decide : 279019565 ≤ 279052333) block2 block3

theorem join_1_0 : (twinPrimeSegment 278921261 279052333).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 278921261 ≤ 278986797)
    (by decide : 278986797 ≤ 279052333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 278921261 279052333).card = 455 := join_1_0

end S133C00
end Sude.GeneratedTwinScan
