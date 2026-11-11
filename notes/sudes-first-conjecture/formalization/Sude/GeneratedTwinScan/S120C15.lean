import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S120C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15926)) 253624365 253657133 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 253624365 253657133).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15926 253624365 253657133
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15927)) 253657133 253689901 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 253657133 253689901).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15927 253657133 253689901
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15928)) 253689901 253722669 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 253689901 253722669).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15928 253689901 253722669
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15929)) 253722669 253755437 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 253722669 253755437).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15929 253722669 253755437
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 253624365 253689901).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 253624365 ≤ 253657133)
    (by decide : 253657133 ≤ 253689901) block0 block1

theorem join_0_1 : (twinPrimeSegment 253689901 253755437).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 253689901 ≤ 253722669)
    (by decide : 253722669 ≤ 253755437) block2 block3

theorem join_1_0 : (twinPrimeSegment 253624365 253755437).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 253624365 ≤ 253689901)
    (by decide : 253689901 ≤ 253755437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 253624365 253755437).card = 450 := join_1_0

end S120C15
end Sude.GeneratedTwinScan
