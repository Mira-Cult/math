import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S213C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21135)) 446693421 446726189 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 446693421 446726189).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21135 446693421 446726189
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21136)) 446726189 446758957 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 446726189 446758957).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21136 446726189 446758957
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21137)) 446758957 446791725 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 446758957 446791725).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21137 446758957 446791725
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21138)) 446791725 446824493 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 446791725 446824493).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21138 446791725 446824493
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 446693421 446758957).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 446693421 ≤ 446726189)
    (by decide : 446726189 ≤ 446758957) block0 block1

theorem join_0_1 : (twinPrimeSegment 446758957 446824493).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 446758957 ≤ 446791725)
    (by decide : 446791725 ≤ 446824493) block2 block3

theorem join_1_0 : (twinPrimeSegment 446693421 446824493).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 446693421 ≤ 446758957)
    (by decide : 446758957 ≤ 446824493) join_0_0 join_0_1

theorem total : (twinPrimeSegment 446693421 446824493).card = 442 := join_1_0

end S213C00
end Sude.GeneratedTwinScan
