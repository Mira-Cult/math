import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S113C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15412)) 237502509 237535277 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 237502509 237535277).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15412 237502509 237535277
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15413)) 237535277 237568045 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 237535277 237568045).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15413 237535277 237568045
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15414)) 237568045 237600813 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 237568045 237600813).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15414 237568045 237600813
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15415)) 237600813 237633581 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 237600813 237633581).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15415 237600813 237633581
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 237502509 237568045).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 237502509 ≤ 237535277)
    (by decide : 237535277 ≤ 237568045) block0 block1

theorem join_0_1 : (twinPrimeSegment 237568045 237633581).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 237568045 ≤ 237600813)
    (by decide : 237600813 ≤ 237633581) block2 block3

theorem join_1_0 : (twinPrimeSegment 237502509 237633581).card = 493 := by
  simpa using combineTwinPrimeSegments (by decide : 237502509 ≤ 237568045)
    (by decide : 237568045 ≤ 237633581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 237502509 237633581).card = 493 := join_1_0

end S113C04
end Sude.GeneratedTwinScan
