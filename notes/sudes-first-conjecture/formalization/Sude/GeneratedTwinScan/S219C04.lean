import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S219C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21443)) 459800621 459833389 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 459800621 459833389).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21443 459800621 459833389
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21444)) 459833389 459866157 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 459833389 459866157).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21444 459833389 459866157
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21445)) 459866157 459898925 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 459866157 459898925).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21445 459866157 459898925
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21446)) 459898925 459931693 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 459898925 459931693).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21446 459898925 459931693
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 459800621 459866157).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 459800621 ≤ 459833389)
    (by decide : 459833389 ≤ 459866157) block0 block1

theorem join_0_1 : (twinPrimeSegment 459866157 459931693).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 459866157 ≤ 459898925)
    (by decide : 459898925 ≤ 459931693) block2 block3

theorem join_1_0 : (twinPrimeSegment 459800621 459931693).card = 459 := by
  simpa using combineTwinPrimeSegments (by decide : 459800621 ≤ 459866157)
    (by decide : 459866157 ≤ 459931693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 459800621 459931693).card = 459 := join_1_0

end S219C04
end Sude.GeneratedTwinScan
