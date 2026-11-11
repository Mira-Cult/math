import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S186C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19777)) 391118893 391151661 = 97 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 391118893 391151661).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19777 391118893 391151661
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19778)) 391151661 391184429 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 391151661 391184429).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19778 391151661 391184429
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19779)) 391184429 391217197 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 391184429 391217197).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19779 391184429 391217197
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19780)) 391217197 391249965 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 391217197 391249965).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19780 391217197 391249965
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 391118893 391184429).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 391118893 ≤ 391151661)
    (by decide : 391151661 ≤ 391184429) block0 block1

theorem join_0_1 : (twinPrimeSegment 391184429 391249965).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 391184429 ≤ 391217197)
    (by decide : 391217197 ≤ 391249965) block2 block3

theorem join_1_0 : (twinPrimeSegment 391118893 391249965).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 391118893 ≤ 391184429)
    (by decide : 391184429 ≤ 391249965) join_0_0 join_0_1

theorem total : (twinPrimeSegment 391118893 391249965).card = 430 := join_1_0

end S186C08
end Sude.GeneratedTwinScan
