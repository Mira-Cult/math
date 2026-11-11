import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S121C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15967)) 254935085 254967853 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 254935085 254967853).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15967 254935085 254967853
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15968)) 254967853 255000621 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 254967853 255000621).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15968 254967853 255000621
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15969)) 255000621 255033389 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 255000621 255033389).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15969 255000621 255033389
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15970)) 255033389 255066157 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 255033389 255066157).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15970 255033389 255066157
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 254935085 255000621).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 254935085 ≤ 254967853)
    (by decide : 254967853 ≤ 255000621) block0 block1

theorem join_0_1 : (twinPrimeSegment 255000621 255066157).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 255000621 ≤ 255033389)
    (by decide : 255033389 ≤ 255066157) block2 block3

theorem join_1_0 : (twinPrimeSegment 254935085 255066157).card = 495 := by
  simpa using combineTwinPrimeSegments (by decide : 254935085 ≤ 255000621)
    (by decide : 255000621 ≤ 255066157) join_0_0 join_0_1

theorem total : (twinPrimeSegment 254935085 255066157).card = 495 := join_1_0

end S121C09
end Sude.GeneratedTwinScan
