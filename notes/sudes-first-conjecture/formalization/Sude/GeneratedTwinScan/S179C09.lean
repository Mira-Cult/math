import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S179C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19406)) 376569901 376602669 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 376569901 376602669).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19406 376569901 376602669
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19407)) 376602669 376635437 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 376602669 376635437).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19407 376602669 376635437
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19407)) 376635437 376668205 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 376635437 376668205).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19407 376635437 376668205
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19408)) 376668205 376700973 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 376668205 376700973).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19408 376668205 376700973
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 376569901 376635437).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 376569901 ≤ 376602669)
    (by decide : 376602669 ≤ 376635437) block0 block1

theorem join_0_1 : (twinPrimeSegment 376635437 376700973).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 376635437 ≤ 376668205)
    (by decide : 376668205 ≤ 376700973) block2 block3

theorem join_1_0 : (twinPrimeSegment 376569901 376700973).card = 431 := by
  simpa using combineTwinPrimeSegments (by decide : 376569901 ≤ 376635437)
    (by decide : 376635437 ≤ 376700973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 376569901 376700973).card = 431 := join_1_0

end S179C09
end Sude.GeneratedTwinScan
