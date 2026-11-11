import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S199C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20442)) 417857581 417890349 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 417857581 417890349).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20442 417857581 417890349
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20443)) 417890349 417923117 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 417890349 417923117).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20443 417890349 417923117
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20443)) 417923117 417955885 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 417923117 417955885).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20443 417923117 417955885
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20444)) 417955885 417988653 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 417955885 417988653).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20444 417955885 417988653
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 417857581 417923117).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 417857581 ≤ 417890349)
    (by decide : 417890349 ≤ 417923117) block0 block1

theorem join_0_1 : (twinPrimeSegment 417923117 417988653).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 417923117 ≤ 417955885)
    (by decide : 417955885 ≤ 417988653) block2 block3

theorem join_1_0 : (twinPrimeSegment 417857581 417988653).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 417857581 ≤ 417923117)
    (by decide : 417923117 ≤ 417988653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 417857581 417988653).card = 442 := join_1_0

end S199C04
end Sude.GeneratedTwinScan
