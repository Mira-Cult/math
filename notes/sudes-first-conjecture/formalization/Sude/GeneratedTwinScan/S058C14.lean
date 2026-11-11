import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S058C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123469869 123502637 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 123469869 123502637).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123469869 123502637
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123502637 123535405 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 123502637 123535405).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123502637 123535405
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123535405 123568173 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 123535405 123568173).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123535405 123568173
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123568173 123600941 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 123568173 123600941).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123568173 123600941
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 123469869 123535405).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 123469869 ≤ 123502637)
    (by decide : 123502637 ≤ 123535405) block0 block1

theorem join_0_1 : (twinPrimeSegment 123535405 123600941).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 123535405 ≤ 123568173)
    (by decide : 123568173 ≤ 123600941) block2 block3

theorem join_1_0 : (twinPrimeSegment 123469869 123600941).card = 495 := by
  simpa using combineTwinPrimeSegments (by decide : 123469869 ≤ 123535405)
    (by decide : 123535405 ≤ 123600941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 123469869 123600941).card = 495 := join_1_0

end S058C14
end Sude.GeneratedTwinScan
