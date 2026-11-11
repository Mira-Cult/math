import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S135C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16834)) 283377709 283410477 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 283377709 283410477).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16834 283377709 283410477
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16835)) 283410477 283443245 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 283410477 283443245).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16835 283410477 283443245
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16836)) 283443245 283476013 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 283443245 283476013).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16836 283443245 283476013
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16837)) 283476013 283508781 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 283476013 283508781).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16837 283476013 283508781
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 283377709 283443245).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 283377709 ≤ 283410477)
    (by decide : 283410477 ≤ 283443245) block0 block1

theorem join_0_1 : (twinPrimeSegment 283443245 283508781).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 283443245 ≤ 283476013)
    (by decide : 283476013 ≤ 283508781) block2 block3

theorem join_1_0 : (twinPrimeSegment 283377709 283508781).card = 419 := by
  simpa using combineTwinPrimeSegments (by decide : 283377709 ≤ 283443245)
    (by decide : 283443245 ≤ 283508781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 283377709 283508781).card = 419 := join_1_0

end S135C02
end Sude.GeneratedTwinScan
