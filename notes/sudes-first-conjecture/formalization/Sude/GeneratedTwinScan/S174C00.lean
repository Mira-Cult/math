import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S174C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19103)) 364904493 364937261 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 364904493 364937261).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19103 364904493 364937261
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19104)) 364937261 364970029 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 364937261 364970029).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19104 364937261 364970029
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19105)) 364970029 365002797 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 364970029 365002797).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19105 364970029 365002797
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19105)) 365002797 365035565 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 365002797 365035565).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19105 365002797 365035565
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 364904493 364970029).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 364904493 ≤ 364937261)
    (by decide : 364937261 ≤ 364970029) block0 block1

theorem join_0_1 : (twinPrimeSegment 364970029 365035565).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 364970029 ≤ 365002797)
    (by decide : 365002797 ≤ 365035565) block2 block3

theorem join_1_0 : (twinPrimeSegment 364904493 365035565).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 364904493 ≤ 364970029)
    (by decide : 364970029 ≤ 365035565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 364904493 365035565).card = 468 := join_1_0

end S174C00
end Sude.GeneratedTwinScan
