import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S235C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22232)) 494272557 494305325 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 494272557 494305325).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22232 494272557 494305325
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22233)) 494305325 494338093 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 494305325 494338093).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22233 494305325 494338093
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22234)) 494338093 494370861 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 494338093 494370861).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22234 494338093 494370861
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22235)) 494370861 494403629 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 494370861 494403629).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22235 494370861 494403629
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 494272557 494338093).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 494272557 ≤ 494305325)
    (by decide : 494305325 ≤ 494338093) block0 block1

theorem join_0_1 : (twinPrimeSegment 494338093 494403629).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 494338093 ≤ 494370861)
    (by decide : 494370861 ≤ 494403629) block2 block3

theorem join_1_0 : (twinPrimeSegment 494272557 494403629).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 494272557 ≤ 494338093)
    (by decide : 494338093 ≤ 494403629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 494272557 494403629).card = 451 := join_1_0

end S235C11
end Sude.GeneratedTwinScan
