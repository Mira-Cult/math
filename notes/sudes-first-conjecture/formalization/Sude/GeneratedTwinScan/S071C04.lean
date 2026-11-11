import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S071C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149422125 149454893 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 149422125 149454893).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149422125 149454893
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149454893 149487661 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 149454893 149487661).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149454893 149487661
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149487661 149520429 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 149487661 149520429).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149487661 149520429
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149520429 149553197 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 149520429 149553197).card = 101 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149520429 149553197
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 149422125 149487661).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 149422125 ≤ 149454893)
    (by decide : 149454893 ≤ 149487661) block0 block1

theorem join_0_1 : (twinPrimeSegment 149487661 149553197).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 149487661 ≤ 149520429)
    (by decide : 149520429 ≤ 149553197) block2 block3

theorem join_1_0 : (twinPrimeSegment 149422125 149553197).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 149422125 ≤ 149487661)
    (by decide : 149487661 ≤ 149553197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 149422125 149553197).card = 449 := join_1_0

end S071C04
end Sude.GeneratedTwinScan
