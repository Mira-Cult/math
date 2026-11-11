import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S094C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14102)) 198836269 198869037 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 198836269 198869037).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14102 198836269 198869037
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14103)) 198869037 198901805 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 198869037 198901805).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14103 198869037 198901805
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14104)) 198901805 198934573 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 198901805 198934573).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14104 198901805 198934573
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14105)) 198934573 198967341 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 198934573 198967341).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14105 198934573 198967341
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 198836269 198901805).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 198836269 ≤ 198869037)
    (by decide : 198869037 ≤ 198901805) block0 block1

theorem join_0_1 : (twinPrimeSegment 198901805 198967341).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 198901805 ≤ 198934573)
    (by decide : 198934573 ≤ 198967341) block2 block3

theorem join_1_0 : (twinPrimeSegment 198836269 198967341).card = 476 := by
  simpa using combineTwinPrimeSegments (by decide : 198836269 ≤ 198901805)
    (by decide : 198901805 ≤ 198967341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 198836269 198967341).card = 476 := join_1_0

end S094C13
end Sude.GeneratedTwinScan
