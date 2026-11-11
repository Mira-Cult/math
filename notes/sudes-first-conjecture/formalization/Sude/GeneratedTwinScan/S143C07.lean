import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S143C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17344)) 300810285 300843053 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 300810285 300843053).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17344 300810285 300843053
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17345)) 300843053 300875821 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 300843053 300875821).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17345 300843053 300875821
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17346)) 300875821 300908589 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 300875821 300908589).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17346 300875821 300908589
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17347)) 300908589 300941357 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 300908589 300941357).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17347 300908589 300941357
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 300810285 300875821).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 300810285 ≤ 300843053)
    (by decide : 300843053 ≤ 300875821) block0 block1

theorem join_0_1 : (twinPrimeSegment 300875821 300941357).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 300875821 ≤ 300908589)
    (by decide : 300908589 ≤ 300941357) block2 block3

theorem join_1_0 : (twinPrimeSegment 300810285 300941357).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 300810285 ≤ 300875821)
    (by decide : 300875821 ≤ 300941357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 300810285 300941357).card = 456 := join_1_0

end S143C07
end Sude.GeneratedTwinScan
