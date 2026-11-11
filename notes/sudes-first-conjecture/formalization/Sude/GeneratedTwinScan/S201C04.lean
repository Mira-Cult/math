import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S201C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20544)) 422051885 422084653 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 422051885 422084653).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20544 422051885 422084653
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20545)) 422084653 422117421 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 422084653 422117421).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20545 422084653 422117421
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20546)) 422117421 422150189 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 422117421 422150189).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20546 422117421 422150189
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20547)) 422150189 422182957 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 422150189 422182957).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20547 422150189 422182957
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 422051885 422117421).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 422051885 ≤ 422084653)
    (by decide : 422084653 ≤ 422117421) block0 block1

theorem join_0_1 : (twinPrimeSegment 422117421 422182957).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 422117421 ≤ 422150189)
    (by decide : 422150189 ≤ 422182957) block2 block3

theorem join_1_0 : (twinPrimeSegment 422051885 422182957).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 422051885 ≤ 422117421)
    (by decide : 422117421 ≤ 422182957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 422051885 422182957).card = 450 := join_1_0

end S201C04
end Sude.GeneratedTwinScan
