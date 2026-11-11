import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S213C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21157)) 447610925 447643693 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 447610925 447643693).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21157 447610925 447643693
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21158)) 447643693 447676461 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 447643693 447676461).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21158 447643693 447676461
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21159)) 447676461 447709229 = 95 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 447676461 447709229).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21159 447676461 447709229
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21159)) 447709229 447741997 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 447709229 447741997).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21159 447709229 447741997
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 447610925 447676461).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 447610925 ≤ 447643693)
    (by decide : 447643693 ≤ 447676461) block0 block1

theorem join_0_1 : (twinPrimeSegment 447676461 447741997).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 447676461 ≤ 447709229)
    (by decide : 447709229 ≤ 447741997) block2 block3

theorem join_1_0 : (twinPrimeSegment 447610925 447741997).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 447610925 ≤ 447676461)
    (by decide : 447676461 ≤ 447741997) join_0_0 join_0_1

theorem total : (twinPrimeSegment 447610925 447741997).card = 426 := join_1_0

end S213C07
end Sude.GeneratedTwinScan
