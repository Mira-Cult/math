import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S230C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21963)) 482345005 482377773 = 88 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 482345005 482377773).card = 88 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21963 482345005 482377773
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21963)) 482377773 482410541 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 482377773 482410541).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21963 482377773 482410541
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21964)) 482410541 482443309 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 482410541 482443309).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21964 482410541 482443309
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21965)) 482443309 482476077 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 482443309 482476077).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21965 482443309 482476077
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 482345005 482410541).card = 198 := by
  simpa using combineTwinPrimeSegments (by decide : 482345005 ≤ 482377773)
    (by decide : 482377773 ≤ 482410541) block0 block1

theorem join_0_1 : (twinPrimeSegment 482410541 482476077).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 482410541 ≤ 482443309)
    (by decide : 482443309 ≤ 482476077) block2 block3

theorem join_1_0 : (twinPrimeSegment 482345005 482476077).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 482345005 ≤ 482410541)
    (by decide : 482410541 ≤ 482476077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 482345005 482476077).card = 436 := join_1_0

end S230C00
end Sude.GeneratedTwinScan
