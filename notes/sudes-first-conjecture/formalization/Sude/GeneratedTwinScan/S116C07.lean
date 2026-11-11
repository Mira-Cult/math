import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S116C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15627)) 244187181 244219949 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 244187181 244219949).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15627 244187181 244219949
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15628)) 244219949 244252717 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 244219949 244252717).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15628 244219949 244252717
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15629)) 244252717 244285485 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 244252717 244285485).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15629 244252717 244285485
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15630)) 244285485 244318253 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 244285485 244318253).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15630 244285485 244318253
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 244187181 244252717).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 244187181 ≤ 244219949)
    (by decide : 244219949 ≤ 244252717) block0 block1

theorem join_0_1 : (twinPrimeSegment 244252717 244318253).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 244252717 ≤ 244285485)
    (by decide : 244285485 ≤ 244318253) block2 block3

theorem join_1_0 : (twinPrimeSegment 244187181 244318253).card = 475 := by
  simpa using combineTwinPrimeSegments (by decide : 244187181 ≤ 244252717)
    (by decide : 244252717 ≤ 244318253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 244187181 244318253).card = 475 := join_1_0

end S116C07
end Sude.GeneratedTwinScan
