import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S189C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19919)) 396754989 396787757 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 396754989 396787757).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19919 396754989 396787757
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19920)) 396787757 396820525 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 396787757 396820525).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19920 396787757 396820525
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19921)) 396820525 396853293 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 396820525 396853293).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19921 396820525 396853293
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19921)) 396853293 396886061 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 396853293 396886061).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19921 396853293 396886061
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 396754989 396820525).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 396754989 ≤ 396787757)
    (by decide : 396787757 ≤ 396820525) block0 block1

theorem join_0_1 : (twinPrimeSegment 396820525 396886061).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 396820525 ≤ 396853293)
    (by decide : 396853293 ≤ 396886061) block2 block3

theorem join_1_0 : (twinPrimeSegment 396754989 396886061).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 396754989 ≤ 396820525)
    (by decide : 396820525 ≤ 396886061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 396754989 396886061).card = 451 := join_1_0

end S189C03
end Sude.GeneratedTwinScan
