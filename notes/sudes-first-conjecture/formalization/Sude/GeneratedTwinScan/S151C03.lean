import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S151C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17807)) 317063213 317095981 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 317063213 317095981).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17807 317063213 317095981
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17808)) 317095981 317128749 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 317095981 317128749).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17808 317095981 317128749
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17809)) 317128749 317161517 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 317128749 317161517).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17809 317128749 317161517
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17809)) 317161517 317194285 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 317161517 317194285).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17809 317161517 317194285
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 317063213 317128749).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 317063213 ≤ 317095981)
    (by decide : 317095981 ≤ 317128749) block0 block1

theorem join_0_1 : (twinPrimeSegment 317128749 317194285).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 317128749 ≤ 317161517)
    (by decide : 317161517 ≤ 317194285) block2 block3

theorem join_1_0 : (twinPrimeSegment 317063213 317194285).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 317063213 ≤ 317128749)
    (by decide : 317128749 ≤ 317194285) join_0_0 join_0_1

theorem total : (twinPrimeSegment 317063213 317194285).card = 434 := join_1_0

end S151C03
end Sude.GeneratedTwinScan
