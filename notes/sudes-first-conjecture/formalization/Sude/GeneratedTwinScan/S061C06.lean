import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S061C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128712749 128745517 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 128712749 128745517).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128712749 128745517
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128745517 128778285 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 128745517 128778285).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128745517 128778285
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128778285 128811053 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 128778285 128811053).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128778285 128811053
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128811053 128843821 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 128811053 128843821).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128811053 128843821
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 128712749 128778285).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 128712749 ≤ 128745517)
    (by decide : 128745517 ≤ 128778285) block0 block1

theorem join_0_1 : (twinPrimeSegment 128778285 128843821).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 128778285 ≤ 128811053)
    (by decide : 128811053 ≤ 128843821) block2 block3

theorem join_1_0 : (twinPrimeSegment 128712749 128843821).card = 493 := by
  simpa using combineTwinPrimeSegments (by decide : 128712749 ≤ 128778285)
    (by decide : 128778285 ≤ 128843821) join_0_0 join_0_1

theorem total : (twinPrimeSegment 128712749 128843821).card = 493 := join_1_0

end S061C06
end Sude.GeneratedTwinScan
