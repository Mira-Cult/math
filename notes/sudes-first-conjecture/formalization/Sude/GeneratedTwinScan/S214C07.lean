import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S214C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21207)) 449708077 449740845 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 449708077 449740845).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21207 449708077 449740845
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21207)) 449740845 449773613 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 449740845 449773613).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21207 449740845 449773613
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21208)) 449773613 449806381 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 449773613 449806381).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21208 449773613 449806381
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21209)) 449806381 449839149 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 449806381 449839149).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21209 449806381 449839149
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 449708077 449773613).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 449708077 ≤ 449740845)
    (by decide : 449740845 ≤ 449773613) block0 block1

theorem join_0_1 : (twinPrimeSegment 449773613 449839149).card = 198 := by
  simpa using combineTwinPrimeSegments (by decide : 449773613 ≤ 449806381)
    (by decide : 449806381 ≤ 449839149) block2 block3

theorem join_1_0 : (twinPrimeSegment 449708077 449839149).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 449708077 ≤ 449773613)
    (by decide : 449773613 ≤ 449839149) join_0_0 join_0_1

theorem total : (twinPrimeSegment 449708077 449839149).card = 449 := join_1_0

end S214C07
end Sude.GeneratedTwinScan
