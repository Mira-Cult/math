import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S030C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63963181 63995949 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 63963181 63995949).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63963181 63995949
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63995949 64028717 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 63995949 64028717).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63995949 64028717
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64028717 64061485 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 64028717 64061485).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64028717 64061485
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64061485 64094253 = 142 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 64061485 64094253).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64061485 64094253
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 63963181 64028717).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 63963181 ≤ 63995949)
    (by decide : 63995949 ≤ 64028717) block0 block1

theorem join_0_1 : (twinPrimeSegment 64028717 64094253).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 64028717 ≤ 64061485)
    (by decide : 64061485 ≤ 64094253) block2 block3

theorem join_1_0 : (twinPrimeSegment 63963181 64094253).card = 517 := by
  simpa using combineTwinPrimeSegments (by decide : 63963181 ≤ 64028717)
    (by decide : 64028717 ≤ 64094253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 63963181 64094253).card = 517 := join_1_0

end S030C08
end Sude.GeneratedTwinScan
