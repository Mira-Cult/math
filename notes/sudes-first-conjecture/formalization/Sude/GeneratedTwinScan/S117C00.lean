import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S117C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15665)) 245366829 245399597 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 245366829 245399597).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15665 245366829 245399597
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15666)) 245399597 245432365 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 245399597 245432365).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15666 245399597 245432365
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15667)) 245432365 245465133 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 245432365 245465133).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15667 245432365 245465133
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15668)) 245465133 245497901 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 245465133 245497901).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15668 245465133 245497901
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 245366829 245432365).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 245366829 ≤ 245399597)
    (by decide : 245399597 ≤ 245432365) block0 block1

theorem join_0_1 : (twinPrimeSegment 245432365 245497901).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 245432365 ≤ 245465133)
    (by decide : 245465133 ≤ 245497901) block2 block3

theorem join_1_0 : (twinPrimeSegment 245366829 245497901).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 245366829 ≤ 245432365)
    (by decide : 245432365 ≤ 245497901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 245366829 245497901).card = 457 := join_1_0

end S117C00
end Sude.GeneratedTwinScan
