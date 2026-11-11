import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S168C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18771)) 352321581 352354349 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 352321581 352354349).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18771 352321581 352354349
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18771)) 352354349 352387117 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 352354349 352387117).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18771 352354349 352387117
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18772)) 352387117 352419885 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 352387117 352419885).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18772 352387117 352419885
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18773)) 352419885 352452653 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 352419885 352452653).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18773 352419885 352452653
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 352321581 352387117).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 352321581 ≤ 352354349)
    (by decide : 352354349 ≤ 352387117) block0 block1

theorem join_0_1 : (twinPrimeSegment 352387117 352452653).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 352387117 ≤ 352419885)
    (by decide : 352419885 ≤ 352452653) block2 block3

theorem join_1_0 : (twinPrimeSegment 352321581 352452653).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 352321581 ≤ 352387117)
    (by decide : 352387117 ≤ 352452653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 352321581 352452653).card = 445 := join_1_0

end S168C00
end Sude.GeneratedTwinScan
