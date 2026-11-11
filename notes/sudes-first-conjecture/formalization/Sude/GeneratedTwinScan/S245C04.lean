import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S245C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22679)) 514326573 514359341 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 514326573 514359341).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22679 514326573 514359341
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22680)) 514359341 514392109 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 514359341 514392109).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22680 514359341 514392109
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22680)) 514392109 514424877 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 514392109 514424877).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22680 514392109 514424877
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22681)) 514424877 514457645 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 514424877 514457645).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22681 514424877 514457645
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 514326573 514392109).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 514326573 ≤ 514359341)
    (by decide : 514359341 ≤ 514392109) block0 block1

theorem join_0_1 : (twinPrimeSegment 514392109 514457645).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 514392109 ≤ 514424877)
    (by decide : 514424877 ≤ 514457645) block2 block3

theorem join_1_0 : (twinPrimeSegment 514326573 514457645).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 514326573 ≤ 514392109)
    (by decide : 514392109 ≤ 514457645) join_0_0 join_0_1

theorem total : (twinPrimeSegment 514326573 514457645).card = 450 := join_1_0

end S245C04
end Sude.GeneratedTwinScan
