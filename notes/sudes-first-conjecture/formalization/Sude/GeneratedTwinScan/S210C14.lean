import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S210C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21030)) 442236973 442269741 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 442236973 442269741).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21030 442236973 442269741
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21030)) 442269741 442302509 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 442269741 442302509).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21030 442269741 442302509
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21031)) 442302509 442335277 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 442302509 442335277).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21031 442302509 442335277
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21032)) 442335277 442368045 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 442335277 442368045).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21032 442335277 442368045
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 442236973 442302509).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 442236973 ≤ 442269741)
    (by decide : 442269741 ≤ 442302509) block0 block1

theorem join_0_1 : (twinPrimeSegment 442302509 442368045).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 442302509 ≤ 442335277)
    (by decide : 442335277 ≤ 442368045) block2 block3

theorem join_1_0 : (twinPrimeSegment 442236973 442368045).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 442236973 ≤ 442302509)
    (by decide : 442302509 ≤ 442368045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 442236973 442368045).card = 427 := join_1_0

end S210C14
end Sude.GeneratedTwinScan
