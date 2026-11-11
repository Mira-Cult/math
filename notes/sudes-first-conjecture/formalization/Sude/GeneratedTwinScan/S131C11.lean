import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S131C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16619)) 276168749 276201517 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 276168749 276201517).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16619 276168749 276201517
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16620)) 276201517 276234285 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 276201517 276234285).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16620 276201517 276234285
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16621)) 276234285 276267053 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 276234285 276267053).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16621 276234285 276267053
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16622)) 276267053 276299821 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 276267053 276299821).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16622 276267053 276299821
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 276168749 276234285).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 276168749 ≤ 276201517)
    (by decide : 276201517 ≤ 276234285) block0 block1

theorem join_0_1 : (twinPrimeSegment 276234285 276299821).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 276234285 ≤ 276267053)
    (by decide : 276267053 ≤ 276299821) block2 block3

theorem join_1_0 : (twinPrimeSegment 276168749 276299821).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 276168749 ≤ 276234285)
    (by decide : 276234285 ≤ 276299821) join_0_0 join_0_1

theorem total : (twinPrimeSegment 276168749 276299821).card = 455 := join_1_0

end S131C11
end Sude.GeneratedTwinScan
