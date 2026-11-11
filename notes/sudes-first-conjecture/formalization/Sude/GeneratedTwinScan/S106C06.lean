import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S106C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14937)) 223084589 223117357 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 223084589 223117357).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14937 223084589 223117357
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14938)) 223117357 223150125 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 223117357 223150125).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14938 223117357 223150125
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14939)) 223150125 223182893 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 223150125 223182893).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14939 223150125 223182893
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14940)) 223182893 223215661 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 223182893 223215661).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14940 223182893 223215661
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 223084589 223150125).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 223084589 ≤ 223117357)
    (by decide : 223117357 ≤ 223150125) block0 block1

theorem join_0_1 : (twinPrimeSegment 223150125 223215661).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 223150125 ≤ 223182893)
    (by decide : 223182893 ≤ 223215661) block2 block3

theorem join_1_0 : (twinPrimeSegment 223084589 223215661).card = 481 := by
  simpa using combineTwinPrimeSegments (by decide : 223084589 ≤ 223150125)
    (by decide : 223150125 ≤ 223215661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 223084589 223215661).card = 481 := join_1_0

end S106C06
end Sude.GeneratedTwinScan
