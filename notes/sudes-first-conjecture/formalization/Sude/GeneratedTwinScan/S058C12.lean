import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S058C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123207725 123240493 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 123207725 123240493).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123207725 123240493
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123240493 123273261 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 123240493 123273261).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123240493 123273261
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123273261 123306029 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 123273261 123306029).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123273261 123306029
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123306029 123338797 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 123306029 123338797).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123306029 123338797
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 123207725 123273261).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 123207725 ≤ 123240493)
    (by decide : 123240493 ≤ 123273261) block0 block1

theorem join_0_1 : (twinPrimeSegment 123273261 123338797).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 123273261 ≤ 123306029)
    (by decide : 123306029 ≤ 123338797) block2 block3

theorem join_1_0 : (twinPrimeSegment 123207725 123338797).card = 508 := by
  simpa using combineTwinPrimeSegments (by decide : 123207725 ≤ 123273261)
    (by decide : 123273261 ≤ 123338797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 123207725 123338797).card = 508 := join_1_0

end S058C12
end Sude.GeneratedTwinScan
