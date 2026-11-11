import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S178C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19365)) 374997037 375029805 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 374997037 375029805).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19365 374997037 375029805
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19366)) 375029805 375062573 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 375029805 375062573).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19366 375029805 375062573
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19367)) 375062573 375095341 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 375062573 375095341).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19367 375062573 375095341
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19368)) 375095341 375128109 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 375095341 375128109).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19368 375095341 375128109
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 374997037 375062573).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 374997037 ≤ 375029805)
    (by decide : 375029805 ≤ 375062573) block0 block1

theorem join_0_1 : (twinPrimeSegment 375062573 375128109).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 375062573 ≤ 375095341)
    (by decide : 375095341 ≤ 375128109) block2 block3

theorem join_1_0 : (twinPrimeSegment 374997037 375128109).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 374997037 ≤ 375062573)
    (by decide : 375062573 ≤ 375128109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 374997037 375128109).card = 471 := join_1_0

end S178C13
end Sude.GeneratedTwinScan
