import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S248C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22817)) 520618029 520650797 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 520618029 520650797).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22817 520618029 520650797
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22818)) 520650797 520683565 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 520650797 520683565).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22818 520650797 520683565
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22819)) 520683565 520716333 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 520683565 520716333).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22819 520683565 520716333
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22819)) 520716333 520749101 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 520716333 520749101).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22819 520716333 520749101
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 520618029 520683565).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 520618029 ≤ 520650797)
    (by decide : 520650797 ≤ 520683565) block0 block1

theorem join_0_1 : (twinPrimeSegment 520683565 520749101).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 520683565 ≤ 520716333)
    (by decide : 520716333 ≤ 520749101) block2 block3

theorem join_1_0 : (twinPrimeSegment 520618029 520749101).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 520618029 ≤ 520683565)
    (by decide : 520683565 ≤ 520749101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 520618029 520749101).card = 433 := join_1_0

end S248C04
end Sude.GeneratedTwinScan
