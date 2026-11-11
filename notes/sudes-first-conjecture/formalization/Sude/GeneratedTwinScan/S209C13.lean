import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S209C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20977)) 440008749 440041517 = 88 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 440008749 440041517).card = 88 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20977 440008749 440041517
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20977)) 440041517 440074285 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 440041517 440074285).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20977 440041517 440074285
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20978)) 440074285 440107053 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 440074285 440107053).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20978 440074285 440107053
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20979)) 440107053 440139821 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 440107053 440139821).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20979 440107053 440139821
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 440008749 440074285).card = 189 := by
  simpa using combineTwinPrimeSegments (by decide : 440008749 ≤ 440041517)
    (by decide : 440041517 ≤ 440074285) block0 block1

theorem join_0_1 : (twinPrimeSegment 440074285 440139821).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 440074285 ≤ 440107053)
    (by decide : 440107053 ≤ 440139821) block2 block3

theorem join_1_0 : (twinPrimeSegment 440008749 440139821).card = 400 := by
  simpa using combineTwinPrimeSegments (by decide : 440008749 ≤ 440074285)
    (by decide : 440074285 ≤ 440139821) join_0_0 join_0_1

theorem total : (twinPrimeSegment 440008749 440139821).card = 400 := join_1_0

end S209C13
end Sude.GeneratedTwinScan
