import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S075C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12620)) 159252525 159285293 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 159252525 159285293).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12620 159252525 159285293
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12622)) 159285293 159318061 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 159285293 159318061).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12622 159285293 159318061
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12623)) 159318061 159350829 = 139 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 159318061 159350829).card = 139 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12623 159318061 159350829
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12624)) 159350829 159383597 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 159350829 159383597).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12624 159350829 159383597
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 159252525 159318061).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 159252525 ≤ 159285293)
    (by decide : 159285293 ≤ 159318061) block0 block1

theorem join_0_1 : (twinPrimeSegment 159318061 159383597).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 159318061 ≤ 159350829)
    (by decide : 159350829 ≤ 159383597) block2 block3

theorem join_1_0 : (twinPrimeSegment 159252525 159383597).card = 492 := by
  simpa using combineTwinPrimeSegments (by decide : 159252525 ≤ 159318061)
    (by decide : 159318061 ≤ 159383597) join_0_0 join_0_1

theorem total : (twinPrimeSegment 159252525 159383597).card = 492 := join_1_0

end S075C15
end Sude.GeneratedTwinScan
