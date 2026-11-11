import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S171C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18979)) 360185901 360218669 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 360185901 360218669).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18979 360185901 360218669
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18980)) 360218669 360251437 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 360218669 360251437).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18980 360218669 360251437
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18981)) 360251437 360284205 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 360251437 360284205).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18981 360251437 360284205
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18982)) 360284205 360316973 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 360284205 360316973).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18982 360284205 360316973
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 360185901 360251437).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 360185901 ≤ 360218669)
    (by decide : 360218669 ≤ 360251437) block0 block1

theorem join_0_1 : (twinPrimeSegment 360251437 360316973).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 360251437 ≤ 360284205)
    (by decide : 360284205 ≤ 360316973) block2 block3

theorem join_1_0 : (twinPrimeSegment 360185901 360316973).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 360185901 ≤ 360251437)
    (by decide : 360251437 ≤ 360316973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 360185901 360316973).card = 462 := join_1_0

end S171C12
end Sude.GeneratedTwinScan
