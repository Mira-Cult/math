import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S046C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98304045 98336813 = 146 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 98304045 98336813).card = 146 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98304045 98336813
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98336813 98369581 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 98336813 98369581).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98336813 98369581
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98369581 98402349 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 98369581 98402349).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98369581 98402349
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98402349 98435117 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 98402349 98435117).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98402349 98435117
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 98304045 98369581).card = 279 := by
  simpa using combineTwinPrimeSegments (by decide : 98304045 ≤ 98336813)
    (by decide : 98336813 ≤ 98369581) block0 block1

theorem join_0_1 : (twinPrimeSegment 98369581 98435117).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 98369581 ≤ 98402349)
    (by decide : 98402349 ≤ 98435117) block2 block3

theorem join_1_0 : (twinPrimeSegment 98304045 98435117).card = 539 := by
  simpa using combineTwinPrimeSegments (by decide : 98304045 ≤ 98369581)
    (by decide : 98369581 ≤ 98435117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 98304045 98435117).card = 539 := join_1_0

end S046C14
end Sude.GeneratedTwinScan
