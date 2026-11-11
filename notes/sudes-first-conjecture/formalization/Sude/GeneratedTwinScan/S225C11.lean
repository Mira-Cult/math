import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S225C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21756)) 473301037 473333805 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 473301037 473333805).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21756 473301037 473333805
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21756)) 473333805 473366573 = 89 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 473333805 473366573).card = 89 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21756 473333805 473366573
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21757)) 473366573 473399341 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 473366573 473399341).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21757 473366573 473399341
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21758)) 473399341 473432109 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 473399341 473432109).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21758 473399341 473432109
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 473301037 473366573).card = 195 := by
  simpa using combineTwinPrimeSegments (by decide : 473301037 ≤ 473333805)
    (by decide : 473333805 ≤ 473366573) block0 block1

theorem join_0_1 : (twinPrimeSegment 473366573 473432109).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 473366573 ≤ 473399341)
    (by decide : 473399341 ≤ 473432109) block2 block3

theorem join_1_0 : (twinPrimeSegment 473301037 473432109).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 473301037 ≤ 473366573)
    (by decide : 473366573 ≤ 473432109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 473301037 473432109).card = 441 := join_1_0

end S225C11
end Sude.GeneratedTwinScan
