import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S247C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22800)) 519831597 519864365 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 519831597 519864365).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22800 519831597 519864365
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22801)) 519864365 519897133 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 519864365 519897133).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22801 519864365 519897133
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22801)) 519897133 519929901 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 519897133 519929901).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22801 519897133 519929901
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22802)) 519929901 519962669 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 519929901 519962669).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22802 519929901 519962669
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 519831597 519897133).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 519831597 ≤ 519864365)
    (by decide : 519864365 ≤ 519897133) block0 block1

theorem join_0_1 : (twinPrimeSegment 519897133 519962669).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 519897133 ≤ 519929901)
    (by decide : 519929901 ≤ 519962669) block2 block3

theorem join_1_0 : (twinPrimeSegment 519831597 519962669).card = 415 := by
  simpa using combineTwinPrimeSegments (by decide : 519831597 ≤ 519897133)
    (by decide : 519897133 ≤ 519962669) join_0_0 join_0_1

theorem total : (twinPrimeSegment 519831597 519962669).card = 415 := join_1_0

end S247C14
end Sude.GeneratedTwinScan
