import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S175C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19199)) 368574509 368607277 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 368574509 368607277).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19199 368574509 368607277
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19200)) 368607277 368640045 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 368607277 368640045).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19200 368607277 368640045
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19200)) 368640045 368672813 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 368640045 368672813).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19200 368640045 368672813
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19201)) 368672813 368705581 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 368672813 368705581).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19201 368672813 368705581
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 368574509 368640045).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 368574509 ≤ 368607277)
    (by decide : 368607277 ≤ 368640045) block0 block1

theorem join_0_1 : (twinPrimeSegment 368640045 368705581).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 368640045 ≤ 368672813)
    (by decide : 368672813 ≤ 368705581) block2 block3

theorem join_1_0 : (twinPrimeSegment 368574509 368705581).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 368574509 ≤ 368640045)
    (by decide : 368640045 ≤ 368705581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 368574509 368705581).card = 440 := join_1_0

end S175C12
end Sude.GeneratedTwinScan
