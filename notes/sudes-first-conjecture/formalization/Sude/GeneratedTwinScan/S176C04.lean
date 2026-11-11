import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S176C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19226)) 369623085 369655853 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 369623085 369655853).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19226 369623085 369655853
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19227)) 369655853 369688621 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 369655853 369688621).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19227 369655853 369688621
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19228)) 369688621 369721389 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 369688621 369721389).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19228 369688621 369721389
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19228)) 369721389 369754157 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 369721389 369754157).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19228 369721389 369754157
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 369623085 369688621).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 369623085 ≤ 369655853)
    (by decide : 369655853 ≤ 369688621) block0 block1

theorem join_0_1 : (twinPrimeSegment 369688621 369754157).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 369688621 ≤ 369721389)
    (by decide : 369721389 ≤ 369754157) block2 block3

theorem join_1_0 : (twinPrimeSegment 369623085 369754157).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 369623085 ≤ 369688621)
    (by decide : 369688621 ≤ 369754157) join_0_0 join_0_1

theorem total : (twinPrimeSegment 369623085 369754157).card = 455 := join_1_0

end S176C04
end Sude.GeneratedTwinScan
