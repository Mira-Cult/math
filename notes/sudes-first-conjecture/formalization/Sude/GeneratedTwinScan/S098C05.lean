import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S098C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14359)) 206176301 206209069 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 206176301 206209069).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14359 206176301 206209069
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14361)) 206209069 206241837 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 206209069 206241837).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14361 206209069 206241837
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14362)) 206241837 206274605 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 206241837 206274605).card = 138 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14362 206241837 206274605
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14363)) 206274605 206307373 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 206274605 206307373).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14363 206274605 206307373
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 206176301 206241837).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 206176301 ≤ 206209069)
    (by decide : 206209069 ≤ 206241837) block0 block1

theorem join_0_1 : (twinPrimeSegment 206241837 206307373).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 206241837 ≤ 206274605)
    (by decide : 206274605 ≤ 206307373) block2 block3

theorem join_1_0 : (twinPrimeSegment 206176301 206307373).card = 504 := by
  simpa using combineTwinPrimeSegments (by decide : 206176301 ≤ 206241837)
    (by decide : 206241837 ≤ 206307373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 206176301 206307373).card = 504 := join_1_0

end S098C05
end Sude.GeneratedTwinScan
