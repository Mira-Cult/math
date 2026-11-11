import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S200C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20528)) 421396525 421429293 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 421396525 421429293).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20528 421396525 421429293
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20529)) 421429293 421462061 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 421429293 421462061).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20529 421429293 421462061
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20530)) 421462061 421494829 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 421462061 421494829).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20530 421462061 421494829
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20531)) 421494829 421527597 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 421494829 421527597).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20531 421494829 421527597
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 421396525 421462061).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 421396525 ≤ 421429293)
    (by decide : 421429293 ≤ 421462061) block0 block1

theorem join_0_1 : (twinPrimeSegment 421462061 421527597).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 421462061 ≤ 421494829)
    (by decide : 421494829 ≤ 421527597) block2 block3

theorem join_1_0 : (twinPrimeSegment 421396525 421527597).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 421396525 ≤ 421462061)
    (by decide : 421462061 ≤ 421527597) join_0_0 join_0_1

theorem total : (twinPrimeSegment 421396525 421527597).card = 434 := join_1_0

end S200C15
end Sude.GeneratedTwinScan
