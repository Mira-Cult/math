import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S085C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13416)) 179961901 179994669 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 179961901 179994669).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13416 179961901 179994669
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13417)) 179994669 180027437 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 179994669 180027437).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13417 179994669 180027437
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13418)) 180027437 180060205 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 180027437 180060205).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13418 180027437 180060205
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13419)) 180060205 180092973 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 180060205 180092973).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13419 180060205 180092973
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 179961901 180027437).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 179961901 ≤ 179994669)
    (by decide : 179994669 ≤ 180027437) block0 block1

theorem join_0_1 : (twinPrimeSegment 180027437 180092973).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 180027437 ≤ 180060205)
    (by decide : 180060205 ≤ 180092973) block2 block3

theorem join_1_0 : (twinPrimeSegment 179961901 180092973).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 179961901 ≤ 180027437)
    (by decide : 180027437 ≤ 180092973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 179961901 180092973).card = 468 := join_1_0

end S085C13
end Sude.GeneratedTwinScan
