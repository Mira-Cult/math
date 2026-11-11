import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S153C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17942)) 321912877 321945645 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 321912877 321945645).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17942 321912877 321945645
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17943)) 321945645 321978413 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 321945645 321978413).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17943 321945645 321978413
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17944)) 321978413 322011181 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 321978413 322011181).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17944 321978413 322011181
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17945)) 322011181 322043949 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 322011181 322043949).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17945 322011181 322043949
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 321912877 321978413).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 321912877 ≤ 321945645)
    (by decide : 321945645 ≤ 321978413) block0 block1

theorem join_0_1 : (twinPrimeSegment 321978413 322043949).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 321978413 ≤ 322011181)
    (by decide : 322011181 ≤ 322043949) block2 block3

theorem join_1_0 : (twinPrimeSegment 321912877 322043949).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 321912877 ≤ 321978413)
    (by decide : 321978413 ≤ 322043949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 321912877 322043949).card = 455 := join_1_0

end S153C08
end Sude.GeneratedTwinScan
