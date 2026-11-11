import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S090C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13801)) 190447661 190480429 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 190447661 190480429).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13801 190447661 190480429
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13802)) 190480429 190513197 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 190480429 190513197).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13802 190480429 190513197
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13803)) 190513197 190545965 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 190513197 190545965).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13803 190513197 190545965
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13805)) 190545965 190578733 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 190545965 190578733).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13805 190545965 190578733
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 190447661 190513197).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 190447661 ≤ 190480429)
    (by decide : 190480429 ≤ 190513197) block0 block1

theorem join_0_1 : (twinPrimeSegment 190513197 190578733).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 190513197 ≤ 190545965)
    (by decide : 190545965 ≤ 190578733) block2 block3

theorem join_1_0 : (twinPrimeSegment 190447661 190578733).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 190447661 ≤ 190513197)
    (by decide : 190513197 ≤ 190578733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 190447661 190578733).card = 457 := join_1_0

end S090C13
end Sude.GeneratedTwinScan
