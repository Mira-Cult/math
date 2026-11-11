import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S056C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118751277 118784045 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 118751277 118784045).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118751277 118784045
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118784045 118816813 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 118784045 118816813).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118784045 118816813
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118816813 118849581 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 118816813 118849581).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118816813 118849581
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118849581 118882349 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 118849581 118882349).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118849581 118882349
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 118751277 118816813).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 118751277 ≤ 118784045)
    (by decide : 118784045 ≤ 118816813) block0 block1

theorem join_0_1 : (twinPrimeSegment 118816813 118882349).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 118816813 ≤ 118849581)
    (by decide : 118849581 ≤ 118882349) block2 block3

theorem join_1_0 : (twinPrimeSegment 118751277 118882349).card = 502 := by
  simpa using combineTwinPrimeSegments (by decide : 118751277 ≤ 118816813)
    (by decide : 118816813 ≤ 118882349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 118751277 118882349).card = 502 := join_1_0

end S056C10
end Sude.GeneratedTwinScan
