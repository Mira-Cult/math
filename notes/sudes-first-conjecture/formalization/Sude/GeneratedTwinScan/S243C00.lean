import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S243C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22575)) 509607981 509640749 = 97 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 509607981 509640749).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22575 509607981 509640749
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22575)) 509640749 509673517 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 509640749 509673517).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22575 509640749 509673517
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22576)) 509673517 509706285 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 509673517 509706285).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22576 509673517 509706285
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22577)) 509706285 509739053 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 509706285 509739053).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22577 509706285 509739053
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 509607981 509673517).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 509607981 ≤ 509640749)
    (by decide : 509640749 ≤ 509673517) block0 block1

theorem join_0_1 : (twinPrimeSegment 509673517 509739053).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 509673517 ≤ 509706285)
    (by decide : 509706285 ≤ 509739053) block2 block3

theorem join_1_0 : (twinPrimeSegment 509607981 509739053).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 509607981 ≤ 509673517)
    (by decide : 509673517 ≤ 509739053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 509607981 509739053).card = 426 := join_1_0

end S243C00
end Sude.GeneratedTwinScan
