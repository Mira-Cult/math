import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S240C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22444)) 503709741 503742509 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 503709741 503742509).card = 138 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22444 503709741 503742509
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22444)) 503742509 503775277 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 503742509 503775277).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22444 503742509 503775277
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22445)) 503775277 503808045 = 87 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 503775277 503808045).card = 87 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22445 503775277 503808045
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22446)) 503808045 503840813 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 503808045 503840813).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22446 503808045 503840813
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 503709741 503775277).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 503709741 ≤ 503742509)
    (by decide : 503742509 ≤ 503775277) block0 block1

theorem join_0_1 : (twinPrimeSegment 503775277 503840813).card = 197 := by
  simpa using combineTwinPrimeSegments (by decide : 503775277 ≤ 503808045)
    (by decide : 503808045 ≤ 503840813) block2 block3

theorem join_1_0 : (twinPrimeSegment 503709741 503840813).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 503709741 ≤ 503775277)
    (by decide : 503775277 ≤ 503840813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 503709741 503840813).card = 436 := join_1_0

end S240C03
end Sude.GeneratedTwinScan
