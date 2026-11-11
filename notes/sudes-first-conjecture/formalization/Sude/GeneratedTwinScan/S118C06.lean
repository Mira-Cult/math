import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S118C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15757)) 248250413 248283181 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 248250413 248283181).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15757 248250413 248283181
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15758)) 248283181 248315949 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 248283181 248315949).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15758 248283181 248315949
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15759)) 248315949 248348717 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 248315949 248348717).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15759 248315949 248348717
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15760)) 248348717 248381485 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 248348717 248381485).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15760 248348717 248381485
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 248250413 248315949).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 248250413 ≤ 248283181)
    (by decide : 248283181 ≤ 248315949) block0 block1

theorem join_0_1 : (twinPrimeSegment 248315949 248381485).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 248315949 ≤ 248348717)
    (by decide : 248348717 ≤ 248381485) block2 block3

theorem join_1_0 : (twinPrimeSegment 248250413 248381485).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 248250413 ≤ 248315949)
    (by decide : 248315949 ≤ 248381485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 248250413 248381485).card = 465 := join_1_0

end S118C06
end Sude.GeneratedTwinScan
