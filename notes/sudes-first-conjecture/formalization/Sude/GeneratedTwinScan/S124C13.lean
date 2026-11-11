import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S124C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16179)) 261750829 261783597 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 261750829 261783597).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16179 261750829 261783597
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16180)) 261783597 261816365 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 261783597 261816365).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16180 261783597 261816365
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16181)) 261816365 261849133 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 261816365 261849133).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16181 261816365 261849133
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16182)) 261849133 261881901 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 261849133 261881901).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16182 261849133 261881901
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 261750829 261816365).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 261750829 ≤ 261783597)
    (by decide : 261783597 ≤ 261816365) block0 block1

theorem join_0_1 : (twinPrimeSegment 261816365 261881901).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 261816365 ≤ 261849133)
    (by decide : 261849133 ≤ 261881901) block2 block3

theorem join_1_0 : (twinPrimeSegment 261750829 261881901).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 261750829 ≤ 261816365)
    (by decide : 261816365 ≤ 261881901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 261750829 261881901).card = 464 := join_1_0

end S124C13
end Sude.GeneratedTwinScan
