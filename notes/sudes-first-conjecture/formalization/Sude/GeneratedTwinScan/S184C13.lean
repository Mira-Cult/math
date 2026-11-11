import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S184C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19687)) 387579949 387612717 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 387579949 387612717).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19687 387579949 387612717
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19688)) 387612717 387645485 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 387612717 387645485).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19688 387612717 387645485
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19689)) 387645485 387678253 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 387645485 387678253).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19689 387645485 387678253
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19690)) 387678253 387711021 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 387678253 387711021).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19690 387678253 387711021
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 387579949 387645485).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 387579949 ≤ 387612717)
    (by decide : 387612717 ≤ 387645485) block0 block1

theorem join_0_1 : (twinPrimeSegment 387645485 387711021).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 387645485 ≤ 387678253)
    (by decide : 387678253 ≤ 387711021) block2 block3

theorem join_1_0 : (twinPrimeSegment 387579949 387711021).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 387579949 ≤ 387645485)
    (by decide : 387645485 ≤ 387711021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 387579949 387711021).card = 447 := join_1_0

end S184C13
end Sude.GeneratedTwinScan
