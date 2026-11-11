import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S057C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120586285 120619053 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 120586285 120619053).card = 104 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120586285 120619053
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120619053 120651821 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 120619053 120651821).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120619053 120651821
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120651821 120684589 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 120651821 120684589).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120651821 120684589
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120684589 120717357 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 120684589 120717357).card = 108 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120684589 120717357
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 120586285 120651821).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 120586285 ≤ 120619053)
    (by decide : 120619053 ≤ 120651821) block0 block1

theorem join_0_1 : (twinPrimeSegment 120651821 120717357).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 120651821 ≤ 120684589)
    (by decide : 120684589 ≤ 120717357) block2 block3

theorem join_1_0 : (twinPrimeSegment 120586285 120717357).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 120586285 ≤ 120651821)
    (by decide : 120651821 ≤ 120717357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 120586285 120717357).card = 467 := join_1_0

end S057C08
end Sude.GeneratedTwinScan
