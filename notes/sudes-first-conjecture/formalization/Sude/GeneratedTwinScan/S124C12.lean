import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S124C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16175)) 261619757 261652525 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 261619757 261652525).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16175 261619757 261652525
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16176)) 261652525 261685293 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 261652525 261685293).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16176 261652525 261685293
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16177)) 261685293 261718061 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 261685293 261718061).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16177 261685293 261718061
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16178)) 261718061 261750829 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 261718061 261750829).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16178 261718061 261750829
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 261619757 261685293).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 261619757 ≤ 261652525)
    (by decide : 261652525 ≤ 261685293) block0 block1

theorem join_0_1 : (twinPrimeSegment 261685293 261750829).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 261685293 ≤ 261718061)
    (by decide : 261718061 ≤ 261750829) block2 block3

theorem join_1_0 : (twinPrimeSegment 261619757 261750829).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 261619757 ≤ 261685293)
    (by decide : 261685293 ≤ 261750829) join_0_0 join_0_1

theorem total : (twinPrimeSegment 261619757 261750829).card = 462 := join_1_0

end S124C12
end Sude.GeneratedTwinScan
