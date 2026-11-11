import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S244C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22665)) 513671213 513703981 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 513671213 513703981).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22665 513671213 513703981
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22665)) 513703981 513736749 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 513703981 513736749).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22665 513703981 513736749
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22666)) 513736749 513769517 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 513736749 513769517).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22666 513736749 513769517
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22667)) 513769517 513802285 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 513769517 513802285).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22667 513769517 513802285
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 513671213 513736749).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 513671213 ≤ 513703981)
    (by decide : 513703981 ≤ 513736749) block0 block1

theorem join_0_1 : (twinPrimeSegment 513736749 513802285).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 513736749 ≤ 513769517)
    (by decide : 513769517 ≤ 513802285) block2 block3

theorem join_1_0 : (twinPrimeSegment 513671213 513802285).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 513671213 ≤ 513736749)
    (by decide : 513736749 ≤ 513802285) join_0_0 join_0_1

theorem total : (twinPrimeSegment 513671213 513802285).card = 430 := join_1_0

end S244C15
end Sude.GeneratedTwinScan
