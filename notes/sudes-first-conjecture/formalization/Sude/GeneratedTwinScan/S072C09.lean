import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S072C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152174637 152207405 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 152174637 152207405).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152174637 152207405
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152207405 152240173 = 96 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 152207405 152240173).card = 96 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152207405 152240173
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152240173 152272941 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 152240173 152272941).card = 109 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152240173 152272941
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152272941 152305709 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 152272941 152305709).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152272941 152305709
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 152174637 152240173).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 152174637 ≤ 152207405)
    (by decide : 152207405 ≤ 152240173) block0 block1

theorem join_0_1 : (twinPrimeSegment 152240173 152305709).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 152240173 ≤ 152272941)
    (by decide : 152272941 ≤ 152305709) block2 block3

theorem join_1_0 : (twinPrimeSegment 152174637 152305709).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 152174637 ≤ 152240173)
    (by decide : 152240173 ≤ 152305709) join_0_0 join_0_1

theorem total : (twinPrimeSegment 152174637 152305709).card = 448 := join_1_0

end S072C09
end Sude.GeneratedTwinScan
