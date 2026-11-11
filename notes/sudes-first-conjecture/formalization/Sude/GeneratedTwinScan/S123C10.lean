import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S123C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16102)) 259260461 259293229 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 259260461 259293229).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16102 259260461 259293229
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16103)) 259293229 259325997 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 259293229 259325997).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16103 259293229 259325997
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16104)) 259325997 259358765 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 259325997 259358765).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16104 259325997 259358765
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16105)) 259358765 259391533 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 259358765 259391533).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16105 259358765 259391533
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 259260461 259325997).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 259260461 ≤ 259293229)
    (by decide : 259293229 ≤ 259325997) block0 block1

theorem join_0_1 : (twinPrimeSegment 259325997 259391533).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 259325997 ≤ 259358765)
    (by decide : 259358765 ≤ 259391533) block2 block3

theorem join_1_0 : (twinPrimeSegment 259260461 259391533).card = 472 := by
  simpa using combineTwinPrimeSegments (by decide : 259260461 ≤ 259325997)
    (by decide : 259325997 ≤ 259391533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 259260461 259391533).card = 472 := join_1_0

end S123C10
end Sude.GeneratedTwinScan
