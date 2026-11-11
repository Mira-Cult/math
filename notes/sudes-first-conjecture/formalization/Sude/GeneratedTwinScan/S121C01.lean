import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S121C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15934)) 253886509 253919277 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 253886509 253919277).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15934 253886509 253919277
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15935)) 253919277 253952045 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 253919277 253952045).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15935 253919277 253952045
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15936)) 253952045 253984813 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 253952045 253984813).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15936 253952045 253984813
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15937)) 253984813 254017581 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 253984813 254017581).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15937 253984813 254017581
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 253886509 253952045).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 253886509 ≤ 253919277)
    (by decide : 253919277 ≤ 253952045) block0 block1

theorem join_0_1 : (twinPrimeSegment 253952045 254017581).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 253952045 ≤ 253984813)
    (by decide : 253984813 ≤ 254017581) block2 block3

theorem join_1_0 : (twinPrimeSegment 253886509 254017581).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 253886509 ≤ 253952045)
    (by decide : 253952045 ≤ 254017581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 253886509 254017581).card = 463 := join_1_0

end S121C01
end Sude.GeneratedTwinScan
