import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S166C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18680)) 348913709 348946477 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 348913709 348946477).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18680 348913709 348946477
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18680)) 348946477 348979245 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 348946477 348979245).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18680 348946477 348979245
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18681)) 348979245 349012013 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 348979245 349012013).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18681 348979245 349012013
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18682)) 349012013 349044781 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 349012013 349044781).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18682 349012013 349044781
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 348913709 348979245).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 348913709 ≤ 348946477)
    (by decide : 348946477 ≤ 348979245) block0 block1

theorem join_0_1 : (twinPrimeSegment 348979245 349044781).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 348979245 ≤ 349012013)
    (by decide : 349012013 ≤ 349044781) block2 block3

theorem join_1_0 : (twinPrimeSegment 348913709 349044781).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 348913709 ≤ 348979245)
    (by decide : 348979245 ≤ 349044781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 348913709 349044781).card = 433 := join_1_0

end S166C06
end Sude.GeneratedTwinScan
