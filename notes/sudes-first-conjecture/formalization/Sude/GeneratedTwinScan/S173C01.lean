import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S173C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19051)) 362938413 362971181 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 362938413 362971181).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19051 362938413 362971181
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19052)) 362971181 363003949 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 362971181 363003949).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19052 362971181 363003949
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19053)) 363003949 363036717 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 363003949 363036717).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19053 363003949 363036717
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19054)) 363036717 363069485 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 363036717 363069485).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19054 363036717 363069485
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 362938413 363003949).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 362938413 ≤ 362971181)
    (by decide : 362971181 ≤ 363003949) block0 block1

theorem join_0_1 : (twinPrimeSegment 363003949 363069485).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 363003949 ≤ 363036717)
    (by decide : 363036717 ≤ 363069485) block2 block3

theorem join_1_0 : (twinPrimeSegment 362938413 363069485).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 362938413 ≤ 363003949)
    (by decide : 363003949 ≤ 363069485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 362938413 363069485).card = 466 := join_1_0

end S173C01
end Sude.GeneratedTwinScan
