import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S079C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12872)) 165675053 165707821 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 165675053 165707821).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12872 165675053 165707821
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12874)) 165707821 165740589 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 165707821 165740589).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12874 165707821 165740589
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12875)) 165740589 165773357 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 165740589 165773357).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12875 165740589 165773357
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12876)) 165773357 165806125 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 165773357 165806125).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12876 165773357 165806125
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 165675053 165740589).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 165675053 ≤ 165707821)
    (by decide : 165707821 ≤ 165740589) block0 block1

theorem join_0_1 : (twinPrimeSegment 165740589 165806125).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 165740589 ≤ 165773357)
    (by decide : 165773357 ≤ 165806125) block2 block3

theorem join_1_0 : (twinPrimeSegment 165675053 165806125).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 165675053 ≤ 165740589)
    (by decide : 165740589 ≤ 165806125) join_0_0 join_0_1

theorem total : (twinPrimeSegment 165675053 165806125).card = 467 := join_1_0

end S079C00
end Sude.GeneratedTwinScan
