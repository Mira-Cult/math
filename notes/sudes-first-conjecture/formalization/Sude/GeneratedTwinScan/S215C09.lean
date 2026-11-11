import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S215C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21262)) 452067373 452100141 = 92 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 452067373 452100141).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21262 452067373 452100141
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21263)) 452100141 452132909 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 452100141 452132909).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21263 452100141 452132909
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21264)) 452132909 452165677 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 452132909 452165677).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21264 452132909 452165677
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21264)) 452165677 452198445 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 452165677 452198445).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21264 452165677 452198445
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 452067373 452132909).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 452067373 ≤ 452100141)
    (by decide : 452100141 ≤ 452132909) block0 block1

theorem join_0_1 : (twinPrimeSegment 452132909 452198445).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 452132909 ≤ 452165677)
    (by decide : 452165677 ≤ 452198445) block2 block3

theorem join_1_0 : (twinPrimeSegment 452067373 452198445).card = 417 := by
  simpa using combineTwinPrimeSegments (by decide : 452067373 ≤ 452132909)
    (by decide : 452132909 ≤ 452198445) join_0_0 join_0_1

theorem total : (twinPrimeSegment 452067373 452198445).card = 417 := join_1_0

end S215C09
end Sude.GeneratedTwinScan
