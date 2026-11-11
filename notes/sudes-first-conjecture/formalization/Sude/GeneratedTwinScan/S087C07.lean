import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S087C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13542)) 183369773 183402541 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 183369773 183402541).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13542 183369773 183402541
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13543)) 183402541 183435309 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 183402541 183435309).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13543 183402541 183435309
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13545)) 183435309 183468077 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 183435309 183468077).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13545 183435309 183468077
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13546)) 183468077 183500845 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 183468077 183500845).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13546 183468077 183500845
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 183369773 183435309).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 183369773 ≤ 183402541)
    (by decide : 183402541 ≤ 183435309) block0 block1

theorem join_0_1 : (twinPrimeSegment 183435309 183500845).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 183435309 ≤ 183468077)
    (by decide : 183468077 ≤ 183500845) block2 block3

theorem join_1_0 : (twinPrimeSegment 183369773 183500845).card = 507 := by
  simpa using combineTwinPrimeSegments (by decide : 183369773 ≤ 183435309)
    (by decide : 183435309 ≤ 183500845) join_0_0 join_0_1

theorem total : (twinPrimeSegment 183369773 183500845).card = 507 := join_1_0

end S087C07
end Sude.GeneratedTwinScan
