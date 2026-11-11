import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S120C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15910)) 253100077 253132845 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 253100077 253132845).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15910 253100077 253132845
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15911)) 253132845 253165613 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 253132845 253165613).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15911 253132845 253165613
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15912)) 253165613 253198381 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 253165613 253198381).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15912 253165613 253198381
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15913)) 253198381 253231149 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 253198381 253231149).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15913 253198381 253231149
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 253100077 253165613).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 253100077 ≤ 253132845)
    (by decide : 253132845 ≤ 253165613) block0 block1

theorem join_0_1 : (twinPrimeSegment 253165613 253231149).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 253165613 ≤ 253198381)
    (by decide : 253198381 ≤ 253231149) block2 block3

theorem join_1_0 : (twinPrimeSegment 253100077 253231149).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 253100077 ≤ 253165613)
    (by decide : 253165613 ≤ 253231149) join_0_0 join_0_1

theorem total : (twinPrimeSegment 253100077 253231149).card = 460 := join_1_0

end S120C11
end Sude.GeneratedTwinScan
