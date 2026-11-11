import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S040C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 83886125 83918893 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 83886125 83918893).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 83886125 83918893
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 83918893 83951661 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 83918893 83951661).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 83918893 83951661
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 83951661 83984429 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 83951661 83984429).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 83951661 83984429
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 83984429 84017197 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 83984429 84017197).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 83984429 84017197
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 83886125 83951661).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 83886125 ≤ 83918893)
    (by decide : 83918893 ≤ 83951661) block0 block1

theorem join_0_1 : (twinPrimeSegment 83951661 84017197).card = 269 := by
  simpa using combineTwinPrimeSegments (by decide : 83951661 ≤ 83984429)
    (by decide : 83984429 ≤ 84017197) block2 block3

theorem join_1_0 : (twinPrimeSegment 83886125 84017197).card = 522 := by
  simpa using combineTwinPrimeSegments (by decide : 83886125 ≤ 83951661)
    (by decide : 83951661 ≤ 84017197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 83886125 84017197).card = 522 := join_1_0

end S040C00
end Sude.GeneratedTwinScan
