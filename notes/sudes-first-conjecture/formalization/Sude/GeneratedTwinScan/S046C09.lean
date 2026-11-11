import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S046C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97648685 97681453 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 97648685 97681453).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97648685 97681453
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97681453 97714221 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 97681453 97714221).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97681453 97714221
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97714221 97746989 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 97714221 97746989).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97714221 97746989
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97746989 97779757 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 97746989 97779757).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97746989 97779757
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 97648685 97714221).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 97648685 ≤ 97681453)
    (by decide : 97681453 ≤ 97714221) block0 block1

theorem join_0_1 : (twinPrimeSegment 97714221 97779757).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 97714221 ≤ 97746989)
    (by decide : 97746989 ≤ 97779757) block2 block3

theorem join_1_0 : (twinPrimeSegment 97648685 97779757).card = 508 := by
  simpa using combineTwinPrimeSegments (by decide : 97648685 ≤ 97714221)
    (by decide : 97714221 ≤ 97779757) join_0_0 join_0_1

theorem total : (twinPrimeSegment 97648685 97779757).card = 508 := join_1_0

end S046C09
end Sude.GeneratedTwinScan
