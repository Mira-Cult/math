import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S092C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13905)) 193331245 193364013 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 193331245 193364013).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13905 193331245 193364013
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13906)) 193364013 193396781 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 193364013 193396781).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13906 193364013 193396781
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13907)) 193396781 193429549 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 193396781 193429549).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13907 193396781 193429549
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13909)) 193429549 193462317 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 193429549 193462317).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13909 193429549 193462317
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 193331245 193396781).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 193331245 ≤ 193364013)
    (by decide : 193364013 ≤ 193396781) block0 block1

theorem join_0_1 : (twinPrimeSegment 193396781 193462317).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 193396781 ≤ 193429549)
    (by decide : 193429549 ≤ 193462317) block2 block3

theorem join_1_0 : (twinPrimeSegment 193331245 193462317).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 193331245 ≤ 193396781)
    (by decide : 193396781 ≤ 193462317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 193331245 193462317).card = 449 := join_1_0

end S092C03
end Sude.GeneratedTwinScan
