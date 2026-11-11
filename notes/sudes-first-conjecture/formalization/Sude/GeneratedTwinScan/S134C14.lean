import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S134C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16819)) 282853421 282886189 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 282853421 282886189).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16819 282853421 282886189
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16820)) 282886189 282918957 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 282886189 282918957).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16820 282886189 282918957
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16821)) 282918957 282951725 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 282918957 282951725).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16821 282918957 282951725
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16822)) 282951725 282984493 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 282951725 282984493).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16822 282951725 282984493
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 282853421 282918957).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 282853421 ≤ 282886189)
    (by decide : 282886189 ≤ 282918957) block0 block1

theorem join_0_1 : (twinPrimeSegment 282918957 282984493).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 282918957 ≤ 282951725)
    (by decide : 282951725 ≤ 282984493) block2 block3

theorem join_1_0 : (twinPrimeSegment 282853421 282984493).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 282853421 ≤ 282918957)
    (by decide : 282918957 ≤ 282984493) join_0_0 join_0_1

theorem total : (twinPrimeSegment 282853421 282984493).card = 446 := join_1_0

end S134C14
end Sude.GeneratedTwinScan
