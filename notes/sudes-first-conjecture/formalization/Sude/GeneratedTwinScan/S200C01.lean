import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S200C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20484)) 419561517 419594285 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 419561517 419594285).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20484 419561517 419594285
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20484)) 419594285 419627053 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 419594285 419627053).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20484 419594285 419627053
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20485)) 419627053 419659821 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 419627053 419659821).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20485 419627053 419659821
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20486)) 419659821 419692589 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 419659821 419692589).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20486 419659821 419692589
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 419561517 419627053).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 419561517 ≤ 419594285)
    (by decide : 419594285 ≤ 419627053) block0 block1

theorem join_0_1 : (twinPrimeSegment 419627053 419692589).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 419627053 ≤ 419659821)
    (by decide : 419659821 ≤ 419692589) block2 block3

theorem join_1_0 : (twinPrimeSegment 419561517 419692589).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 419561517 ≤ 419627053)
    (by decide : 419627053 ≤ 419692589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 419561517 419692589).card = 432 := join_1_0

end S200C01
end Sude.GeneratedTwinScan
