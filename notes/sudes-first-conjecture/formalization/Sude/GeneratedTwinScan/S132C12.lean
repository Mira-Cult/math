import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S132C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16686)) 278396973 278429741 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 278396973 278429741).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16686 278396973 278429741
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16687)) 278429741 278462509 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 278429741 278462509).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16687 278429741 278462509
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16688)) 278462509 278495277 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 278462509 278495277).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16688 278462509 278495277
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16689)) 278495277 278528045 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 278495277 278528045).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16689 278495277 278528045
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 278396973 278462509).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 278396973 ≤ 278429741)
    (by decide : 278429741 ≤ 278462509) block0 block1

theorem join_0_1 : (twinPrimeSegment 278462509 278528045).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 278462509 ≤ 278495277)
    (by decide : 278495277 ≤ 278528045) block2 block3

theorem join_1_0 : (twinPrimeSegment 278396973 278528045).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 278396973 ≤ 278462509)
    (by decide : 278462509 ≤ 278528045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 278396973 278528045).card = 467 := join_1_0

end S132C12
end Sude.GeneratedTwinScan
