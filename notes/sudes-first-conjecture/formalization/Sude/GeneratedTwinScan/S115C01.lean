import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S115C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15535)) 241303597 241336365 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 241303597 241336365).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15535 241303597 241336365
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15536)) 241336365 241369133 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 241336365 241369133).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15536 241336365 241369133
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15537)) 241369133 241401901 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 241369133 241401901).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15537 241369133 241401901
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15538)) 241401901 241434669 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 241401901 241434669).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15538 241401901 241434669
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 241303597 241369133).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 241303597 ≤ 241336365)
    (by decide : 241336365 ≤ 241369133) block0 block1

theorem join_0_1 : (twinPrimeSegment 241369133 241434669).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 241369133 ≤ 241401901)
    (by decide : 241401901 ≤ 241434669) block2 block3

theorem join_1_0 : (twinPrimeSegment 241303597 241434669).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 241303597 ≤ 241369133)
    (by decide : 241369133 ≤ 241434669) join_0_0 join_0_1

theorem total : (twinPrimeSegment 241303597 241434669).card = 462 := join_1_0

end S115C01
end Sude.GeneratedTwinScan
