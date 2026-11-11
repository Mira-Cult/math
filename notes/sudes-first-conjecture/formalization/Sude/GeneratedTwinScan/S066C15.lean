import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S066C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140378157 140410925 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 140378157 140410925).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140378157 140410925
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140410925 140443693 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 140410925 140443693).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140410925 140443693
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140443693 140476461 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 140443693 140476461).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140443693 140476461
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140476461 140509229 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 140476461 140509229).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140476461 140509229
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 140378157 140443693).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 140378157 ≤ 140410925)
    (by decide : 140410925 ≤ 140443693) block0 block1

theorem join_0_1 : (twinPrimeSegment 140443693 140509229).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 140443693 ≤ 140476461)
    (by decide : 140476461 ≤ 140509229) block2 block3

theorem join_1_0 : (twinPrimeSegment 140378157 140509229).card = 483 := by
  simpa using combineTwinPrimeSegments (by decide : 140378157 ≤ 140443693)
    (by decide : 140443693 ≤ 140509229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 140378157 140509229).card = 483 := join_1_0

end S066C15
end Sude.GeneratedTwinScan
