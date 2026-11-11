import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S213C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21138)) 446824493 446857261 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 446824493 446857261).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21138 446824493 446857261
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21139)) 446857261 446890029 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 446857261 446890029).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21139 446857261 446890029
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21140)) 446890029 446922797 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 446890029 446922797).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21140 446890029 446922797
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21141)) 446922797 446955565 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 446922797 446955565).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21141 446922797 446955565
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 446824493 446890029).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 446824493 ≤ 446857261)
    (by decide : 446857261 ≤ 446890029) block0 block1

theorem join_0_1 : (twinPrimeSegment 446890029 446955565).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 446890029 ≤ 446922797)
    (by decide : 446922797 ≤ 446955565) block2 block3

theorem join_1_0 : (twinPrimeSegment 446824493 446955565).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 446824493 ≤ 446890029)
    (by decide : 446890029 ≤ 446955565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 446824493 446955565).card = 442 := join_1_0

end S213C01
end Sude.GeneratedTwinScan
