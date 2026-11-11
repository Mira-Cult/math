import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S232C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22070)) 487063597 487096365 = 91 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 487063597 487096365).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22070 487063597 487096365
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22071)) 487096365 487129133 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 487096365 487129133).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22071 487096365 487129133
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22071)) 487129133 487161901 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 487129133 487161901).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22071 487129133 487161901
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22072)) 487161901 487194669 = 95 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 487161901 487194669).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22072 487161901 487194669
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 487063597 487129133).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 487063597 ≤ 487096365)
    (by decide : 487096365 ≤ 487129133) block0 block1

theorem join_0_1 : (twinPrimeSegment 487129133 487194669).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 487129133 ≤ 487161901)
    (by decide : 487161901 ≤ 487194669) block2 block3

theorem join_1_0 : (twinPrimeSegment 487063597 487194669).card = 414 := by
  simpa using combineTwinPrimeSegments (by decide : 487063597 ≤ 487129133)
    (by decide : 487129133 ≤ 487194669) join_0_0 join_0_1

theorem total : (twinPrimeSegment 487063597 487194669).card = 414 := join_1_0

end S232C04
end Sude.GeneratedTwinScan
