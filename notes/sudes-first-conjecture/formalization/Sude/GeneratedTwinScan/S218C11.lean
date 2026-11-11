import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S218C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21416)) 458620973 458653741 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 458620973 458653741).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21416 458620973 458653741
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21416)) 458653741 458686509 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 458653741 458686509).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21416 458653741 458686509
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21417)) 458686509 458719277 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 458686509 458719277).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21417 458686509 458719277
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21418)) 458719277 458752045 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 458719277 458752045).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21418 458719277 458752045
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 458620973 458686509).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 458620973 ≤ 458653741)
    (by decide : 458653741 ≤ 458686509) block0 block1

theorem join_0_1 : (twinPrimeSegment 458686509 458752045).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 458686509 ≤ 458719277)
    (by decide : 458719277 ≤ 458752045) block2 block3

theorem join_1_0 : (twinPrimeSegment 458620973 458752045).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 458620973 ≤ 458686509)
    (by decide : 458686509 ≤ 458752045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 458620973 458752045).card = 452 := join_1_0

end S218C11
end Sude.GeneratedTwinScan
