import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S085C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13386)) 179175469 179208237 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 179175469 179208237).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13386 179175469 179208237
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13388)) 179208237 179241005 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 179208237 179241005).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13388 179208237 179241005
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13389)) 179241005 179273773 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 179241005 179273773).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13389 179241005 179273773
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13390)) 179273773 179306541 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 179273773 179306541).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13390 179273773 179306541
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 179175469 179241005).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 179175469 ≤ 179208237)
    (by decide : 179208237 ≤ 179241005) block0 block1

theorem join_0_1 : (twinPrimeSegment 179241005 179306541).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 179241005 ≤ 179273773)
    (by decide : 179273773 ≤ 179306541) block2 block3

theorem join_1_0 : (twinPrimeSegment 179175469 179306541).card = 488 := by
  simpa using combineTwinPrimeSegments (by decide : 179175469 ≤ 179241005)
    (by decide : 179241005 ≤ 179306541) join_0_0 join_0_1

theorem total : (twinPrimeSegment 179175469 179306541).card = 488 := join_1_0

end S085C07
end Sude.GeneratedTwinScan
