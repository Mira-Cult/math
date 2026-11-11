import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S112C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15356)) 235798573 235831341 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 235798573 235831341).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15356 235798573 235831341
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15357)) 235831341 235864109 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 235831341 235864109).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15357 235831341 235864109
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15358)) 235864109 235896877 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 235864109 235896877).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15358 235864109 235896877
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15360)) 235896877 235929645 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 235896877 235929645).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15360 235896877 235929645
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 235798573 235864109).card = 269 := by
  simpa using combineTwinPrimeSegments (by decide : 235798573 ≤ 235831341)
    (by decide : 235831341 ≤ 235864109) block0 block1

theorem join_0_1 : (twinPrimeSegment 235864109 235929645).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 235864109 ≤ 235896877)
    (by decide : 235896877 ≤ 235929645) block2 block3

theorem join_1_0 : (twinPrimeSegment 235798573 235929645).card = 512 := by
  simpa using combineTwinPrimeSegments (by decide : 235798573 ≤ 235864109)
    (by decide : 235864109 ≤ 235929645) join_0_0 join_0_1

theorem total : (twinPrimeSegment 235798573 235929645).card = 512 := join_1_0

end S112C07
end Sude.GeneratedTwinScan
