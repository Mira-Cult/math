import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S090C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13739)) 188743725 188776493 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 188743725 188776493).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13739 188743725 188776493
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13740)) 188776493 188809261 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 188776493 188809261).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13740 188776493 188809261
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13741)) 188809261 188842029 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 188809261 188842029).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13741 188809261 188842029
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13743)) 188842029 188874797 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 188842029 188874797).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13743 188842029 188874797
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 188743725 188809261).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 188743725 ≤ 188776493)
    (by decide : 188776493 ≤ 188809261) block0 block1

theorem join_0_1 : (twinPrimeSegment 188809261 188874797).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 188809261 ≤ 188842029)
    (by decide : 188842029 ≤ 188874797) block2 block3

theorem join_1_0 : (twinPrimeSegment 188743725 188874797).card = 476 := by
  simpa using combineTwinPrimeSegments (by decide : 188743725 ≤ 188809261)
    (by decide : 188809261 ≤ 188874797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 188743725 188874797).card = 476 := join_1_0

end S090C00
end Sude.GeneratedTwinScan
