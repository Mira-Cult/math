import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S124C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16139)) 260440109 260472877 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 260440109 260472877).card = 138 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16139 260440109 260472877
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16140)) 260472877 260505645 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 260472877 260505645).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16140 260472877 260505645
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16141)) 260505645 260538413 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 260505645 260538413).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16141 260505645 260538413
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16142)) 260538413 260571181 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 260538413 260571181).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16142 260538413 260571181
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 260440109 260505645).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 260440109 ≤ 260472877)
    (by decide : 260472877 ≤ 260505645) block0 block1

theorem join_0_1 : (twinPrimeSegment 260505645 260571181).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 260505645 ≤ 260538413)
    (by decide : 260538413 ≤ 260571181) block2 block3

theorem join_1_0 : (twinPrimeSegment 260440109 260571181).card = 491 := by
  simpa using combineTwinPrimeSegments (by decide : 260440109 ≤ 260505645)
    (by decide : 260505645 ≤ 260571181) join_0_0 join_0_1

theorem total : (twinPrimeSegment 260440109 260571181).card = 491 := join_1_0

end S124C03
end Sude.GeneratedTwinScan
