import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S071C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150208557 150241325 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 150208557 150241325).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150208557 150241325
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150241325 150274093 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 150241325 150274093).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150241325 150274093
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150274093 150306861 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 150274093 150306861).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150274093 150306861
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150306861 150339629 = 144 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 150306861 150339629).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150306861 150339629
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 150208557 150274093).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 150208557 ≤ 150241325)
    (by decide : 150241325 ≤ 150274093) block0 block1

theorem join_0_1 : (twinPrimeSegment 150274093 150339629).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 150274093 ≤ 150306861)
    (by decide : 150306861 ≤ 150339629) block2 block3

theorem join_1_0 : (twinPrimeSegment 150208557 150339629).card = 515 := by
  simpa using combineTwinPrimeSegments (by decide : 150208557 ≤ 150274093)
    (by decide : 150274093 ≤ 150339629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 150208557 150339629).card = 515 := join_1_0

end S071C10
end Sude.GeneratedTwinScan
