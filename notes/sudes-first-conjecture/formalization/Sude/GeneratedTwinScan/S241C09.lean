import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S241C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22508)) 506593325 506626093 = 81 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 506593325 506626093).card = 81 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22508 506593325 506626093
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22509)) 506626093 506658861 = 97 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 506626093 506658861).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22509 506626093 506658861
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22509)) 506658861 506691629 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 506658861 506691629).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22509 506658861 506691629
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22510)) 506691629 506724397 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 506691629 506724397).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22510 506691629 506724397
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 506593325 506658861).card = 178 := by
  simpa using combineTwinPrimeSegments (by decide : 506593325 ≤ 506626093)
    (by decide : 506626093 ≤ 506658861) block0 block1

theorem join_0_1 : (twinPrimeSegment 506658861 506724397).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 506658861 ≤ 506691629)
    (by decide : 506691629 ≤ 506724397) block2 block3

theorem join_1_0 : (twinPrimeSegment 506593325 506724397).card = 392 := by
  simpa using combineTwinPrimeSegments (by decide : 506593325 ≤ 506658861)
    (by decide : 506658861 ≤ 506724397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 506593325 506724397).card = 392 := join_1_0

end S241C09
end Sude.GeneratedTwinScan
