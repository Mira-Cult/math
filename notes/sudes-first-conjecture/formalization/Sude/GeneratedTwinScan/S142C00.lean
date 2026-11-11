import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S142C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17257)) 297795629 297828397 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 297795629 297828397).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17257 297795629 297828397
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17258)) 297828397 297861165 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 297828397 297861165).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17258 297828397 297861165
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17259)) 297861165 297893933 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 297861165 297893933).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17259 297861165 297893933
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17260)) 297893933 297926701 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 297893933 297926701).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17260 297893933 297926701
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 297795629 297861165).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 297795629 ≤ 297828397)
    (by decide : 297828397 ≤ 297861165) block0 block1

theorem join_0_1 : (twinPrimeSegment 297861165 297926701).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 297861165 ≤ 297893933)
    (by decide : 297893933 ≤ 297926701) block2 block3

theorem join_1_0 : (twinPrimeSegment 297795629 297926701).card = 459 := by
  simpa using combineTwinPrimeSegments (by decide : 297795629 ≤ 297861165)
    (by decide : 297861165 ≤ 297926701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 297795629 297926701).card = 459 := join_1_0

end S142C00
end Sude.GeneratedTwinScan
