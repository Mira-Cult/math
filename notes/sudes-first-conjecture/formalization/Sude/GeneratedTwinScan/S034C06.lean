import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S034C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72089645 72122413 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 72089645 72122413).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72089645 72122413
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72122413 72155181 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 72122413 72155181).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72122413 72155181
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72155181 72187949 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 72155181 72187949).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72155181 72187949
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72187949 72220717 = 140 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 72187949 72220717).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72187949 72220717
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 72089645 72155181).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 72089645 ≤ 72122413)
    (by decide : 72122413 ≤ 72155181) block0 block1

theorem join_0_1 : (twinPrimeSegment 72155181 72220717).card = 273 := by
  simpa using combineTwinPrimeSegments (by decide : 72155181 ≤ 72187949)
    (by decide : 72187949 ≤ 72220717) block2 block3

theorem join_1_0 : (twinPrimeSegment 72089645 72220717).card = 544 := by
  simpa using combineTwinPrimeSegments (by decide : 72089645 ≤ 72155181)
    (by decide : 72155181 ≤ 72220717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 72089645 72220717).card = 544 := join_1_0

end S034C06
end Sude.GeneratedTwinScan
