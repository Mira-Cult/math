import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S193C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20125)) 405012525 405045293 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 405012525 405045293).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20125 405012525 405045293
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20126)) 405045293 405078061 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 405045293 405078061).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20126 405045293 405078061
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20127)) 405078061 405110829 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 405078061 405110829).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20127 405078061 405110829
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20128)) 405110829 405143597 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 405110829 405143597).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20128 405110829 405143597
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 405012525 405078061).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 405012525 ≤ 405045293)
    (by decide : 405045293 ≤ 405078061) block0 block1

theorem join_0_1 : (twinPrimeSegment 405078061 405143597).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 405078061 ≤ 405110829)
    (by decide : 405110829 ≤ 405143597) block2 block3

theorem join_1_0 : (twinPrimeSegment 405012525 405143597).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 405012525 ≤ 405078061)
    (by decide : 405078061 ≤ 405143597) join_0_0 join_0_1

theorem total : (twinPrimeSegment 405012525 405143597).card = 434 := join_1_0

end S193C02
end Sude.GeneratedTwinScan
